/* Calculate branch probabilities, and basic block execution counts.
   Copyright (C) 1990-2017 Free Software Foundation, Inc.
   Contributed by James E. Wilson, UC Berkeley/Cygnus Support;
   based on some ideas from Dain Samples of UC Berkeley.
   Further mangling by Bob Manson, Cygnus Support.
   Converted to use trees by Dale Johannesen, Apple Computer.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 3, or (at your option) any later
version.

GCC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

/* Generate basic block profile instrumentation and auxiliary files.
   Tree-based version.  See profile.c for overview.  */

#include "config.h"
#define INCLUDE_ALGORITHM
#include "system.h"
#include "coretypes.h"
#include "memmodel.h"
#include "backend.h"
#include "target.h"
#include "tree.h"
#include "gimple.h"
#include "cfghooks.h"
#include "tree-pass.h"
#include "ssa.h"
#include "cgraph.h"
#include "coverage.h"
#include "diagnostic-core.h"
#include "fold-const.h"
#include "varasm.h"
#include "tree-nested.h"
#include "gimplify.h"
#include "gimple-iterator.h"
#include "gimplify-me.h"
#include "tree-cfg.h"
#include "tree-into-ssa.h"
#include "value-prof.h"
#include "profile.h"
#include "tree-cfgcleanup.h"
#include "params.h"
#include "stringpool.h"
#include "attribs.h"
#include "cfganal.h"
#include "cfgloop.h"
#include "gimple-pretty-print.h"

static GTY(()) tree gcov_type_node;
static GTY(()) tree tree_interval_profiler_fn;
static GTY(()) tree tree_pow2_profiler_fn;
static GTY(()) tree tree_one_value_profiler_fn;
static GTY(()) tree tree_indirect_call_profiler_fn;
static GTY(()) tree tree_average_profiler_fn;
static GTY(()) tree tree_ior_profiler_fn;
static GTY(()) tree tree_time_profiler_counter;


static GTY(()) tree ic_void_ptr_var;
static GTY(()) tree ic_gcov_type_ptr_var;
static GTY(()) tree ptr_void;

namespace {

struct mcdc_ctx {
    /* output arrays */
    basic_block *blocks;
    int *sizes;

    /* the size of the blocks buffer */
    int maxelems;

    /*
     * number of expressions found; how many counters must be allocated.
     *
     * must be smaller than maxelem. Describes the number of blocks+sizes
     * written.
     *
     * Can be replaced by popcount (seen)
     */
    int exprs;

    /*
     * dominating or first-in-expr basic blocks seen; this effectively stops
     * loop edges from being taken again
     */
    auto_sbitmap seen;

    explicit mcdc_ctx (unsigned size) : maxelems (0), exprs (0), seen (size) {}

    void commit (basic_block top, int nblocks) {
        blocks   += nblocks;
        *sizes   += nblocks;
        maxelems -= nblocks;

        exprs++;
        sizes++;
        *sizes = 0;

        bitmap_set_bit (seen, top->index);
    }
};

}

void print(const basic_block* blocks, int size, const char* s = "") {
    return;
    printf("%s [ ", s);
    for (int i = 0; i < size; i++)
        printf("%d ", blocks[i]->index);
    printf("]\n");
}

void print(basic_block entry, basic_block exit) {
    return;
    puts(current_function_name());
    basic_block bb;
    FOR_BB_BETWEEN(bb, entry, exit, next_bb)
    {
        edge e; edge_iterator ei;
        FOR_EACH_EDGE(e, ei, bb->succs) {
            printf("A%d -> A%d\n", e->src->index, e->dest->index);
        }
    }
}

void print(edge e) {
    return;
    printf ("==== EDGE %d -> %d ====\n", e->src->index, e->dest->index);
    gimple_stmt_iterator i;
    for (i = gsi_start (e->insns.g); !gsi_end_p (i); gsi_next (&i))
    {
        gimple* gs = gsi_stmt(i);
        print_gimple_stmt (stdout, gs, 0, TDF_SLIM);
    }

    printf ("====             ====\n");
}

static int
index_of (const_basic_block needle, const const_basic_block* blocks, int size)
{
    for (int i = 0; i < size; i++) {
        if (blocks[i] == needle)
            return i;
    }
    return -1;
}

static bool
index_lt (const basic_block x, const basic_block y)
{
    return x->index < y->index;
}

/*
 * Find masked conditions
 */
static int
chase_masked_conditions (
    basic_block block,
    const basic_block *expr,
    int nexpr,
    const unsigned* flag,
    basic_block *out,
    int maxsize)
{
    edge e;
    edge_iterator ei;
    int n = 0;
    FOR_EACH_EDGE (e, ei, block->preds) {
        /*
         * Skip any predecessor not in the expression - there might be such an
         * edge to the enclosing expression or in the presence of loops, but
         * masking cannot happen outside the expression itself.
         *
         * Expressions should generally be small enough that linear search is
         * fast, but this could just as well be a bitmap.
         */
        if (index_of (e->src, expr, nexpr) == -1)
            continue;

        if (e->flags & flag[0])
            out[n++] = e->src;
    }

    for (int pos = 0; pos < n; pos++)
    {
        block = out[pos];
        FOR_EACH_EDGE (e, ei, block->preds)
        {
            /*
             * Stop on previously-seen node, since all its predecessor have
             * been added already. Maintaining it as a set also keeps the size
             * of the output bounded to the size of the expression.
             */
            if (index_of (e->src, out, n) != -1)
                continue;

            if (index_of (e->src, expr, nexpr) == -1)
                continue;

            if (e->flags & flag[1])
                out[n++] = e->src;

            if (n == maxsize)
                return -1;
        }
    }

    return n;
}

/*
 * Walk the blocks formed by the expression(s) and look for conditions that
 * would mask other conditions.
 *
 * Consider A || B. If B is true then A will does not independently affect the
 * decision. In a way, this is "reverse" short circuiting, and always work on
 * the right-hand side of expressions. A || B interpreted as binary decision
 * diagram becomes:
 *
 * A
 *t|\f
 * | \
 * |  B
 * |t/ \f
 * |/   \
 * T     F
 *
 * The algorithm looks for "closed paths" like the one between ATB. Masking
 * right-hand sides happen when a block has a pair of incoming edges of the
 * same boolean value, and there is an edge connecting the two predecessors
 * with the *opposite* boolean value. In this particular example:
 *
 * A(t) -> T
 * A(f) -> B
 * B(t) -> T
 *
 * Notice that the masking block is B, and the masked block is A. It gets
 * slightly more complicated, since masking can affect "outside" its own
 * subexpression. For example, A || (B && C). If C is false, B is masked.
 * However, if B && C is true, A gets masked. B && C can be determined from C,
 * since !B would terminate and not evaluate C, so a true C would mask A.
 *
 * A
 *t|\f
 * | \
 * |  \
 * |   \
 * |    B
 * |  t/ \f
 * |  C   |
 * |t/ \f |
 * |/   \ |
 * T     F
 *
 * Notice how BFC forms a "closed path" on a decision false. Previous
 * subexpressions are masked by walking the tree upwards until:
 *  + there are no edges with the same truth value
 *  + it reaches the root
 * In this particular example, C would mask B (directly), and mask A because
 * the edge AB is false.
 */

static void
mask_dontcare_subexprs (const basic_block* blocks, gcov_type_unsigned* masks, int nblocks)
{

    memset (masks, 0, sizeof (*masks) * nblocks * 2);

    #define MCDC_MAX_TERMS 64
    basic_block eblocks[MCDC_MAX_TERMS];
    for (int i = 0; i < nblocks; i++)
    {
        basic_block block = blocks[i];

        if (single_pred_p (block))
            continue;

        const unsigned flags[] = {
            EDGE_TRUE_VALUE,
            EDGE_FALSE_VALUE,
            EDGE_TRUE_VALUE,
        };

        for (int k = 0; k < 2; k++)
        {
            int n = chase_masked_conditions
                (block, blocks, nblocks, flags + k, eblocks, MCDC_MAX_TERMS);

            if (n < 2)
                continue;

            basic_block highest = eblocks[0];
            for (int i = 1; i < n; i++)
                if (eblocks[i]->index > highest->index)
                    highest = eblocks[i];

            const int idst = index_of (highest, blocks, nblocks);
            gcc_assert (idst != -1);

            for (int i = 0; i < n; i++) {
                if (highest == eblocks[i])
                    continue;

                const int pos = index_of (eblocks[i], blocks, nblocks);
                masks[2*idst + k] |= gcov_type_unsigned (1) << pos;
            }
        }
    }

    #undef MCDC_MAX_TERMS
}

static void
zero_accumulator_on_function_entry (tree accumulator, basic_block block)
{
    edge e;
    edge_iterator ei;
    tree zero = build_int_cst (gcov_type_node, 0);
    FOR_EACH_EDGE (e, ei, block->succs)
        gsi_insert_on_edge (e, gimple_build_assign (accumulator, zero));
}

static int
find_expr_limits (basic_block pre, basic_block* out, int maxsize, basic_block post, sbitmap expr)
{
    gcc_assert (maxsize > 0);

    edge e;
    edge_iterator ei;

    basic_block loop = pre->loop_father->header;
    int n = 0;
    out[n++] = pre;
    bitmap_set_bit (expr, pre->index);

    for (int pos = 0; pos < n; pos++) {
        basic_block block = out[pos];

        FOR_EACH_EDGE (e, ei, block->succs) {
            basic_block dest = e->dest;
            /* Skip loop edges, as they go outside the expression */
            if (dest == loop)
                continue;

            if (dest == post)
                continue;

            if (single_succ_p (dest))
                continue;

            /* already-seen, don't re-add */
            if (bitmap_bit_p (expr, dest->index))
                continue;

            bitmap_set_bit (expr, dest->index);
            out[n++] = dest;
            if (n == maxsize)
                return n;
        }
    }

    return n;
}

static int
find_expr_halo (basic_block* blocks, int nblocks)
{
    edge e;
    edge_iterator ei;
    int n = 0;
    basic_block* exits = blocks + nblocks;
    for (int i = 0; i < nblocks; i++) {
        FOR_EACH_EDGE (e, ei, blocks[i]->succs) {
            if (index_of (e->dest, blocks, nblocks + n) != -1)
                continue;

            exits[n++] = e->dest;
        }
    }

    return n;
}

/*
 * Find and isolate the first expression between two dominators.
 *
 * Either block of a conditional could have more decisions and loops, so
 * isolate the first decision by set-intersecting all paths from the
 * post-dominator to the entry block.
 *
 * The function returns the number of blocks from n that make up the leading
 * expression in prefix order (i.e. the order expected by the instrumenting
 * code). When this function returns 0 there are no decisions between pre and
 * post, and this segment of the CFG can safely be skipped.
 *
 * The post nodes can have predecessors that do not belong to this subgraph,
 * which are skipped. This is expected, for example when there is a conditional
 * in the else-block of a larger expression:
 *
 * if (A) {
 *    if (B) {}
 * } else {
 *    if (C) {} else {}
 * }
 *
 *           A
 *        t / \ f
 *         /   \
 *        B     C
 *       /\    / \
 *      /  \  T   F
 *     T    \  \ /
 *      \   |   o
 *       \  |  /
 *        \ | /
 *         \|/
 *          E
 *
 * Processing [B, E) which looks like:
 *
 *    B
 *   /|
 *  / |
 * T  |
 *  \ /
 *   E ----> o // predecessor outside [B, e)
 */

static void
dfsup (sbitmap reachable, basic_block pre, basic_block sink, basic_block* stack)
{
    if (bitmap_bit_p (reachable, pre->index))
        return;

    edge e;
    edge_iterator ei;
    stack[0] = pre;
    bitmap_set_bit (reachable, pre->index);

    for (int n = 0; n >= 0; n--) {
        FOR_EACH_EDGE (e, ei, stack[n]->preds) {
            if (bitmap_bit_p (reachable, e->src->index))
                continue;

            if (!dominated_by_p (CDI_POST_DOMINATORS, e->src, sink))
                continue;

            bitmap_set_bit (reachable, e->src->index);
            stack[n++] = e->src;
        }
    }
}

static void
dfsup1 (sbitmap reachable, basic_block pre, basic_block post, basic_block* stack)
{
    if (bitmap_bit_p (reachable, pre->index))
        return;

    edge e;
    edge_iterator ei;
    stack[0] = pre;
    bitmap_set_bit (reachable, pre->index);
    bitmap_set_bit (reachable, post->index);

    for (int n = 0; n >= 0; n--) {
        FOR_EACH_EDGE (e, ei, stack[n]->preds) {
            if (bitmap_bit_p (reachable, e->src->index))
                continue;

            bitmap_set_bit (reachable, e->src->index);
            stack[n++] = e->src;
        }
    }
}

static int
find_first_expr (basic_block pre, basic_block post, basic_block* blocks, int maxsize)
{
    if (single_succ_p (pre))
        return 0;

    edge e;
    edge_iterator ei;

    const int nmax = n_basic_blocks_for_fn (cfun);
    auto_sbitmap expr (nmax);
    auto_sbitmap reachable (nmax);

    struct loop* loop = pre->loop_father;
    const bool dowhile = !loop_exits_from_bb_p (loop, pre);
    if (bb_loop_header_p (pre) && !dowhile) {
        /* if this is a do-while loop, the loop-condition goes to latch */
        /* TODO: document why it does not apply to do-while */
        basic_block loopexit = NULL;
        FOR_EACH_EDGE (e, ei, pre->succs) {
            if (loop_exit_edge_p (loop, e)) {
                loopexit = e->dest;
                break;
            }
        }
        gcc_assert (loopexit);

        dfsup1 (expr, loopexit, pre, blocks);
        FOR_EACH_EDGE (e, ei, pre->preds)
            if (dominated_by_p (CDI_DOMINATORS, e->src, pre))
                bitmap_set_bit (expr, e->src->index);

        basic_block b;
        FOR_BB_BETWEEN (b, pre, post, next_bb) {
            if (!bitmap_bit_p (expr, b->index))
                continue;

            if (single_succ_p (b)) {
                bitmap_clear_bit (expr, b->index);
                continue;
            }

            FOR_EACH_EDGE (e, ei, b->succs) {
                if (!bitmap_bit_p (expr, e->dest->index)) {
                    bitmap_clear_bit (expr, b->index);
                    break;
                }
            }
        }
        /*
         * The post dominator bit will be when walking the graph, but should
         * never be in the output. The pre/entry node *must* be, but since the
         * graph is walked "upwards" with the pre as bound, it is never
         * included.
         */
        bitmap_clear_bit (expr, post->index);
        bitmap_set_bit (expr, pre->index);

        int k = 0;
        FOR_BB_BETWEEN (b, pre, post, next_bb)
            if (bitmap_bit_p (expr, b->index))
                blocks[k++] = b;

        return k;
    }

    int nblocks = find_expr_limits (pre, blocks, maxsize, post, expr);

    // <-- only need this bit!!
    // problem is conditional-in-loop because nothing prunes children
    if (nblocks == 1)
        return 1;

    FOR_EACH_EDGE (e, ei, post->preds) {
        if (!dominated_by_p (CDI_DOMINATORS, e->src, pre))
            continue;

        bitmap_clear (reachable);
        bitmap_set_bit (reachable, pre->index);
        dfsup (reachable, e->src, post, blocks + nblocks);
        bitmap_and (expr, expr, reachable);
    }

    int k = 0;
    for (int i = 0; i < nblocks; i++)
        if (bitmap_bit_p (expr, blocks[i]->index))
            blocks[k++] = blocks[i];
    nblocks = k;

    if (nblocks < 2)
        return nblocks;

    /* record all nodes immediately outside of */
    int nexits = find_expr_halo (blocks, nblocks);
    if (nexits == 2)
        return nblocks;

    /* then, dfs + intersect from there */
    basic_block *exits = blocks + nblocks;
    for (int i = 0; i < nexits; i++) {
        FOR_EACH_EDGE (e, ei, exits[i]->preds) {
            if (!dominated_by_p (CDI_DOMINATORS, e->src, pre))
                continue;

            bitmap_clear (reachable);
            dfsup1 (reachable, e->src, pre, exits + nexits);
            bitmap_and (expr, expr, reachable);
        }
    }

    k = 0;
    for (int i = 0; i < nblocks; i++)
        if (bitmap_bit_p (expr, blocks[i]->index))
            blocks[k++] = blocks[i];
    nblocks = k;

    return nblocks;
}

/*
 * This is a (slightly) modified version of the algorithm in Whalen, Heimdahl,
 * De Silva "Efficient Test Coverage Measurement for MC/DC". Their algorithm
 * work on ASTs, but the instrumentation work on control flow graphs.
 *
 * The instrumentation relies heavily on all decision with the same boolean
 * value have the same *index* in the successor vector. If this is not the
 * case, some other method must be used to determine which successor correspond
 * to which boolean value.
 *
 * The algorithm does not consider the symbol of a condition, only its
 * position, which means !A || (!B && A) is considered 3-term conditional.
 *
 * The algorithm work recognises three main graph shapes:
 * * The loop
 * * Nested expressions
 * * Conditionals
 *
 * For all cases the high-level approach is similar: find the post dominator to
 * the entry node, and do a depth-first search for the dominator. The entry
 * and exit might be a subgraph of the function.
 *
 * If the dominator is a loop, find all nodes in the expression *before* the
 * loop entry, which makes up the the loop condition. Then, recursively process
 * the loop body, before continuing from the dominator.
 *
 * Otherwise, isolate the boolean expression by searching from the post
 * dominator feeding the result into set intersections. The only blocks
 * remaining are the ones in common in all paths, which are the blocks that
 * make up the first decision. If there are sub expressions (with decisions)
 * left, the function is called recursively to sort them out.
 *
 * TODO: describe output
 */

static void
find_conditions_between (mcdc_ctx& ctx, basic_block entry, basic_block exit)
{
    edge e;
    edge_iterator ei;

    basic_block pre;
    basic_block post;
    for (pre = entry ;; pre = post) {
        if (pre == exit)
            break;
        if (bitmap_bit_p (ctx.seen, pre->index))
            break;

        post = get_immediate_dominator (CDI_POST_DOMINATORS, pre);
        int nblocks = find_first_expr (pre, post, ctx.blocks, ctx.maxelems);
        if (nblocks == 0)
            continue;

        // TODO: document
        std::sort(ctx.blocks, ctx.blocks + nblocks, index_lt);
        basic_block last = ctx.blocks[nblocks - 1];
        FOR_EACH_EDGE (e, ei, last->succs)
            ctx.blocks[nblocks++] = e->dest;
        ctx.commit (pre, nblocks);

        FOR_EACH_EDGE (e, ei, last->succs)
            find_conditions_between (ctx, e->dest, post);
    }
}

int
find_condition_blocks (
    basic_block entry,
    basic_block exit,
    basic_block *blocks,
    int *sizes,
    int maxsize)
{
    record_loop_exits ();
    if (!dom_info_available_p (CDI_POST_DOMINATORS))
        calculate_dominance_info (CDI_POST_DOMINATORS);

    if (!dom_info_available_p (CDI_DOMINATORS))
        calculate_dominance_info (CDI_DOMINATORS);

    mcdc_ctx ctx (maxsize);
    ctx.blocks = blocks;
    ctx.sizes = sizes + 1;
    ctx.maxelems = maxsize;
    sizes[0] = sizes[1] = 0;
    find_conditions_between (ctx, entry, exit);

    /* partial sum */
    for (int i = 0; i < ctx.exprs; ++i)
        sizes[i + 1] += sizes[i];

    return ctx.exprs;
}

static void
emit_bitexpr (edge e, tree lhs, tree op1, tree_code op, tree op2)
{
    tree tmp;
    gassign *read;
    gassign *bitw;
    gassign *write;
    /*
     * insert lhs = op1 <bit-op> op2, e.g. lhs = op1 | op2
     */
    tmp   = make_temp_ssa_name  (gcov_type_node, NULL, "__mcdc_tmp");
    read  = gimple_build_assign (tmp, op1);
    tmp   = make_temp_ssa_name  (gcov_type_node, NULL, "__mcdc_tmp");
    bitw  = gimple_build_assign (tmp, op, gimple_assign_lhs (read), op2);
    write = gimple_build_assign (lhs, gimple_assign_lhs (bitw));

    gsi_insert_on_edge (e, read);
    gsi_insert_on_edge (e, bitw);
    gsi_insert_on_edge (e, write);
}

int instrument_decision (basic_block *blocks, int nblocks, int idx_decision)
{
    gcc_assert (nblocks > 2);

    tree accu[2] = {
        build_decl (
            UNKNOWN_LOCATION,
            VAR_DECL,
            get_identifier("__gcov_mcdc_accu_true"),
            gcov_type_node
        ),
        build_decl (
            UNKNOWN_LOCATION,
            VAR_DECL,
            get_identifier("__gcov_mcdc_accu_false"),
            gcov_type_node
        ),
    };
    zero_accumulator_on_function_entry
        (accu[0], ENTRY_BLOCK_PTR_FOR_FN (cfun));
    zero_accumulator_on_function_entry
        (accu[1], ENTRY_BLOCK_PTR_FOR_FN (cfun));

    gcov_type_unsigned  masks_static[64];
    gcov_type_unsigned *masks_dynamic = NULL;
    gcov_type_unsigned *masks;
    gcc_assert (sizeof (*masks) == sizeof (uint64_t));
    if ((size_t)nblocks * 2 < sizeof (masks_static) / sizeof (masks_static[0]))
      {
        masks = masks_static;
      }
    else
      {
        masks_dynamic = XNEWVEC (gcov_type_unsigned, nblocks * 2);
        masks = masks_dynamic;
      }

    mask_dontcare_subexprs (blocks, masks, nblocks);
    int condition = 0;

    /* TODO: -2 because of true/false exit blocks */
    for (int iblock = 0; iblock < nblocks - 2; iblock++)
    {
        basic_block block = blocks[iblock];

        if (single_succ_p (block))
            continue;

        for (int k = 0; k < 2; k++)
        {
            edge e = EDGE_SUCC (block, k);
            const int t = !!!(e->flags & EDGE_TRUE_VALUE);

            /* accu[k] |= condition[i] */
            tree rhs = build_int_cst (gcov_type_node, 1ULL << condition);
            emit_bitexpr (e, accu[t], accu[t], BIT_IOR_EXPR, rhs);

            if (masks[2*condition + t] == 0)
                continue;

            /* accu[k] &= ~mask[k] */
            gcov_type_unsigned mask = masks[2*condition + t];
            for (int j = 0; j < 2; j++) {
                rhs = build_int_cst (gcov_type_node, ~mask);
                emit_bitexpr (e, accu[j], accu[j], BIT_AND_EXPR, rhs);
            }
        }

        condition++;
    }

    edge e;
    edge_iterator ei;
    basic_block exit = EXIT_BLOCK_PTR_FOR_FN (cfun);
    FOR_EACH_EDGE (e, ei, exit->preds)
    {
        /* independent[k] |= accu[k] */
        for (int k = 0; k < 2; k++) {
            tree ref = tree_coverage_counter_ref (GCOV_COUNTER_MCDC, 2*idx_decision + k);

            tree tmp = make_temp_ssa_name (gcov_type_node, NULL, "__mcdc_tmp");
            gassign *read = gimple_build_assign (tmp, ref);
            gsi_insert_on_edge (e, read);

            tree rop = gimple_assign_lhs (read);
            emit_bitexpr (e, unshare_expr (ref), accu[k], BIT_IOR_EXPR, rop);
        }
    }

    free (masks_dynamic);
    return condition;
}

/* Do initialization work for the edge profiler.  */

/* Add code:
   __thread gcov*	__gcov_indirect_call_counters; // pointer to actual counter
   __thread void*	__gcov_indirect_call_callee; // actual callee address
   __thread int __gcov_function_counter; // time profiler function counter
*/
static void
init_ic_make_global_vars (void)
{
  tree gcov_type_ptr;

  ptr_void = build_pointer_type (void_type_node);

  ic_void_ptr_var
    = build_decl (UNKNOWN_LOCATION, VAR_DECL,
		  get_identifier (
			  (PARAM_VALUE (PARAM_INDIR_CALL_TOPN_PROFILE) ?
			   "__gcov_indirect_call_topn_callee" :
			   "__gcov_indirect_call_callee")),
		  ptr_void);
  TREE_PUBLIC (ic_void_ptr_var) = 1;
  DECL_EXTERNAL (ic_void_ptr_var) = 1;
  TREE_STATIC (ic_void_ptr_var) = 1;
  DECL_ARTIFICIAL (ic_void_ptr_var) = 1;
  DECL_INITIAL (ic_void_ptr_var) = NULL;
  if (targetm.have_tls)
    set_decl_tls_model (ic_void_ptr_var, decl_default_tls_model (ic_void_ptr_var));

  gcov_type_ptr = build_pointer_type (get_gcov_type ());

  ic_gcov_type_ptr_var
    = build_decl (UNKNOWN_LOCATION, VAR_DECL,
		  get_identifier (
			  (PARAM_VALUE (PARAM_INDIR_CALL_TOPN_PROFILE) ?
			   "__gcov_indirect_call_topn_counters" :
			   "__gcov_indirect_call_counters")),
		  gcov_type_ptr);
  TREE_PUBLIC (ic_gcov_type_ptr_var) = 1;
  DECL_EXTERNAL (ic_gcov_type_ptr_var) = 1;
  TREE_STATIC (ic_gcov_type_ptr_var) = 1;
  DECL_ARTIFICIAL (ic_gcov_type_ptr_var) = 1;
  DECL_INITIAL (ic_gcov_type_ptr_var) = NULL;
  if (targetm.have_tls)
    set_decl_tls_model (ic_gcov_type_ptr_var, decl_default_tls_model (ic_gcov_type_ptr_var));
}

/* Create the type and function decls for the interface with gcov.  */

void
gimple_init_gcov_profiler (void)
{
  tree interval_profiler_fn_type;
  tree pow2_profiler_fn_type;
  tree one_value_profiler_fn_type;
  tree gcov_type_ptr;
  tree ic_profiler_fn_type;
  tree average_profiler_fn_type;
  const char *profiler_fn_name;
  const char *fn_name;

  if (!gcov_type_node)
    {
      const char *fn_suffix
	= flag_profile_update == PROFILE_UPDATE_ATOMIC ? "_atomic" : "";

      gcov_type_node = get_gcov_type ();
      gcov_type_ptr = build_pointer_type (gcov_type_node);

      /* void (*) (gcov_type *, gcov_type, int, unsigned)  */
      interval_profiler_fn_type
	      = build_function_type_list (void_type_node,
					  gcov_type_ptr, gcov_type_node,
					  integer_type_node,
					  unsigned_type_node, NULL_TREE);
      fn_name = concat ("__gcov_interval_profiler", fn_suffix, NULL);
      tree_interval_profiler_fn = build_fn_decl (fn_name,
						 interval_profiler_fn_type);
      free (CONST_CAST (char *, fn_name));
      TREE_NOTHROW (tree_interval_profiler_fn) = 1;
      DECL_ATTRIBUTES (tree_interval_profiler_fn)
	= tree_cons (get_identifier ("leaf"), NULL,
		     DECL_ATTRIBUTES (tree_interval_profiler_fn));

      /* void (*) (gcov_type *, gcov_type)  */
      pow2_profiler_fn_type
	      = build_function_type_list (void_type_node,
					  gcov_type_ptr, gcov_type_node,
					  NULL_TREE);
      fn_name = concat ("__gcov_pow2_profiler", fn_suffix, NULL);
      tree_pow2_profiler_fn = build_fn_decl (fn_name, pow2_profiler_fn_type);
      free (CONST_CAST (char *, fn_name));
      TREE_NOTHROW (tree_pow2_profiler_fn) = 1;
      DECL_ATTRIBUTES (tree_pow2_profiler_fn)
	= tree_cons (get_identifier ("leaf"), NULL,
		     DECL_ATTRIBUTES (tree_pow2_profiler_fn));

      /* void (*) (gcov_type *, gcov_type)  */
      one_value_profiler_fn_type
	      = build_function_type_list (void_type_node,
					  gcov_type_ptr, gcov_type_node,
					  NULL_TREE);
      fn_name = concat ("__gcov_one_value_profiler", fn_suffix, NULL);
      tree_one_value_profiler_fn = build_fn_decl (fn_name,
						  one_value_profiler_fn_type);
      free (CONST_CAST (char *, fn_name));
      TREE_NOTHROW (tree_one_value_profiler_fn) = 1;
      DECL_ATTRIBUTES (tree_one_value_profiler_fn)
	= tree_cons (get_identifier ("leaf"), NULL,
		     DECL_ATTRIBUTES (tree_one_value_profiler_fn));

      init_ic_make_global_vars ();

      /* void (*) (gcov_type, void *)  */
      ic_profiler_fn_type
	       = build_function_type_list (void_type_node,
					  gcov_type_node,
					  ptr_void,
					  NULL_TREE);
      profiler_fn_name = "__gcov_indirect_call_profiler_v2";
      if (PARAM_VALUE (PARAM_INDIR_CALL_TOPN_PROFILE))
	profiler_fn_name = "__gcov_indirect_call_topn_profiler";

      tree_indirect_call_profiler_fn
	      = build_fn_decl (profiler_fn_name, ic_profiler_fn_type);

      TREE_NOTHROW (tree_indirect_call_profiler_fn) = 1;
      DECL_ATTRIBUTES (tree_indirect_call_profiler_fn)
	= tree_cons (get_identifier ("leaf"), NULL,
		     DECL_ATTRIBUTES (tree_indirect_call_profiler_fn));

      tree_time_profiler_counter
	= build_decl (UNKNOWN_LOCATION, VAR_DECL,
		      get_identifier ("__gcov_time_profiler_counter"),
		      get_gcov_type ());
      TREE_PUBLIC (tree_time_profiler_counter) = 1;
      DECL_EXTERNAL (tree_time_profiler_counter) = 1;
      TREE_STATIC (tree_time_profiler_counter) = 1;
      DECL_ARTIFICIAL (tree_time_profiler_counter) = 1;
      DECL_INITIAL (tree_time_profiler_counter) = NULL;

      /* void (*) (gcov_type *, gcov_type)  */
      average_profiler_fn_type
	      = build_function_type_list (void_type_node,
					  gcov_type_ptr, gcov_type_node, NULL_TREE);
      fn_name = concat ("__gcov_average_profiler", fn_suffix, NULL);
      tree_average_profiler_fn = build_fn_decl (fn_name,
						average_profiler_fn_type);
      free (CONST_CAST (char *, fn_name));
      TREE_NOTHROW (tree_average_profiler_fn) = 1;
      DECL_ATTRIBUTES (tree_average_profiler_fn)
	= tree_cons (get_identifier ("leaf"), NULL,
		     DECL_ATTRIBUTES (tree_average_profiler_fn));
      fn_name = concat ("__gcov_ior_profiler", fn_suffix, NULL);
      tree_ior_profiler_fn = build_fn_decl (fn_name, average_profiler_fn_type);
      free (CONST_CAST (char *, fn_name));
      TREE_NOTHROW (tree_ior_profiler_fn) = 1;
      DECL_ATTRIBUTES (tree_ior_profiler_fn)
	= tree_cons (get_identifier ("leaf"), NULL,
		     DECL_ATTRIBUTES (tree_ior_profiler_fn));

      /* LTO streamer needs assembler names.  Because we create these decls
         late, we need to initialize them by hand.  */
      DECL_ASSEMBLER_NAME (tree_interval_profiler_fn);
      DECL_ASSEMBLER_NAME (tree_pow2_profiler_fn);
      DECL_ASSEMBLER_NAME (tree_one_value_profiler_fn);
      DECL_ASSEMBLER_NAME (tree_indirect_call_profiler_fn);
      DECL_ASSEMBLER_NAME (tree_average_profiler_fn);
      DECL_ASSEMBLER_NAME (tree_ior_profiler_fn);
    }
}

/* Output instructions as GIMPLE trees to increment the edge
   execution count, and insert them on E.  We rely on
   gsi_insert_on_edge to preserve the order.  */

void
gimple_gen_edge_profiler (int edgeno, edge e)
{
  tree one;

  one = build_int_cst (gcov_type_node, 1);

  if (flag_profile_update == PROFILE_UPDATE_ATOMIC)
    {
      /* __atomic_fetch_add (&counter, 1, MEMMODEL_RELAXED); */
      tree addr = tree_coverage_counter_addr (GCOV_COUNTER_ARCS, edgeno);
      tree f = builtin_decl_explicit (LONG_LONG_TYPE_SIZE > 32
				      ? BUILT_IN_ATOMIC_FETCH_ADD_8:
				      BUILT_IN_ATOMIC_FETCH_ADD_4);
      gcall *stmt = gimple_build_call (f, 3, addr, one,
				       build_int_cst (integer_type_node,
						      MEMMODEL_RELAXED));
      gsi_insert_on_edge (e, stmt);
    }
  else
    {
      tree ref = tree_coverage_counter_ref (GCOV_COUNTER_ARCS, edgeno);
      tree gcov_type_tmp_var = make_temp_ssa_name (gcov_type_node,
						   NULL, "PROF_edge_counter");
      gassign *stmt1 = gimple_build_assign (gcov_type_tmp_var, ref);
      gcov_type_tmp_var = make_temp_ssa_name (gcov_type_node,
					      NULL, "PROF_edge_counter");
      gassign *stmt2 = gimple_build_assign (gcov_type_tmp_var, PLUS_EXPR,
					    gimple_assign_lhs (stmt1), one);
      gassign *stmt3 = gimple_build_assign (unshare_expr (ref),
					    gimple_assign_lhs (stmt2));
      gsi_insert_on_edge (e, stmt1);
      gsi_insert_on_edge (e, stmt2);
      gsi_insert_on_edge (e, stmt3);
    }
}

/* Emits code to get VALUE to instrument at GSI, and returns the
   variable containing the value.  */

static tree
prepare_instrumented_value (gimple_stmt_iterator *gsi, histogram_value value)
{
  tree val = value->hvalue.value;
  if (POINTER_TYPE_P (TREE_TYPE (val)))
    val = fold_convert (build_nonstandard_integer_type
			  (TYPE_PRECISION (TREE_TYPE (val)), 1), val);
  return force_gimple_operand_gsi (gsi, fold_convert (gcov_type_node, val),
				   true, NULL_TREE, true, GSI_SAME_STMT);
}

/* Output instructions as GIMPLE trees to increment the interval histogram
   counter.  VALUE is the expression whose value is profiled.  TAG is the
   tag of the section for counters, BASE is offset of the counter position.  */

void
gimple_gen_interval_profiler (histogram_value value, unsigned tag, unsigned base)
{
  gimple *stmt = value->hvalue.stmt;
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
  tree ref = tree_coverage_counter_ref (tag, base), ref_ptr;
  gcall *call;
  tree val;
  tree start = build_int_cst_type (integer_type_node,
				   value->hdata.intvl.int_start);
  tree steps = build_int_cst_type (unsigned_type_node,
				   value->hdata.intvl.steps);

  ref_ptr = force_gimple_operand_gsi (&gsi,
				      build_addr (ref),
				      true, NULL_TREE, true, GSI_SAME_STMT);
  val = prepare_instrumented_value (&gsi, value);
  call = gimple_build_call (tree_interval_profiler_fn, 4,
			    ref_ptr, val, start, steps);
  gsi_insert_before (&gsi, call, GSI_NEW_STMT);
}

/* Output instructions as GIMPLE trees to increment the power of two histogram
   counter.  VALUE is the expression whose value is profiled.  TAG is the tag
   of the section for counters, BASE is offset of the counter position.  */

void
gimple_gen_pow2_profiler (histogram_value value, unsigned tag, unsigned base)
{
  gimple *stmt = value->hvalue.stmt;
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
  tree ref_ptr = tree_coverage_counter_addr (tag, base);
  gcall *call;
  tree val;

  ref_ptr = force_gimple_operand_gsi (&gsi, ref_ptr,
				      true, NULL_TREE, true, GSI_SAME_STMT);
  val = prepare_instrumented_value (&gsi, value);
  call = gimple_build_call (tree_pow2_profiler_fn, 2, ref_ptr, val);
  gsi_insert_before (&gsi, call, GSI_NEW_STMT);
}

/* Output instructions as GIMPLE trees for code to find the most common value.
   VALUE is the expression whose value is profiled.  TAG is the tag of the
   section for counters, BASE is offset of the counter position.  */

void
gimple_gen_one_value_profiler (histogram_value value, unsigned tag, unsigned base)
{
  gimple *stmt = value->hvalue.stmt;
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
  tree ref_ptr = tree_coverage_counter_addr (tag, base);
  gcall *call;
  tree val;

  ref_ptr = force_gimple_operand_gsi (&gsi, ref_ptr,
				      true, NULL_TREE, true, GSI_SAME_STMT);
  val = prepare_instrumented_value (&gsi, value);
  call = gimple_build_call (tree_one_value_profiler_fn, 2, ref_ptr, val);
  gsi_insert_before (&gsi, call, GSI_NEW_STMT);
}


/* Output instructions as GIMPLE trees for code to find the most
   common called function in indirect call.
   VALUE is the call expression whose indirect callee is profiled.
   TAG is the tag of the section for counters, BASE is offset of the
   counter position.  */

void
gimple_gen_ic_profiler (histogram_value value, unsigned tag, unsigned base)
{
  tree tmp1;
  gassign *stmt1, *stmt2, *stmt3;
  gimple *stmt = value->hvalue.stmt;
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
  tree ref_ptr = tree_coverage_counter_addr (tag, base);

  if ( (PARAM_VALUE (PARAM_INDIR_CALL_TOPN_PROFILE) &&
        tag == GCOV_COUNTER_V_INDIR) ||
       (!PARAM_VALUE (PARAM_INDIR_CALL_TOPN_PROFILE) &&
        tag == GCOV_COUNTER_ICALL_TOPNV))
    return;

  ref_ptr = force_gimple_operand_gsi (&gsi, ref_ptr,
				      true, NULL_TREE, true, GSI_SAME_STMT);

  /* Insert code:

    stmt1: __gcov_indirect_call_counters = get_relevant_counter_ptr ();
    stmt2: tmp1 = (void *) (indirect call argument value)
    stmt3: __gcov_indirect_call_callee = tmp1;
   */

  stmt1 = gimple_build_assign (ic_gcov_type_ptr_var, ref_ptr);
  tmp1 = make_temp_ssa_name (ptr_void, NULL, "PROF");
  stmt2 = gimple_build_assign (tmp1, unshare_expr (value->hvalue.value));
  stmt3 = gimple_build_assign (ic_void_ptr_var, gimple_assign_lhs (stmt2));

  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt2, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt3, GSI_SAME_STMT);
}


/* Output instructions as GIMPLE trees for code to find the most
   common called function in indirect call. Insert instructions at the
   beginning of every possible called function.
  */

void
gimple_gen_ic_func_profiler (void)
{
  struct cgraph_node * c_node = cgraph_node::get (current_function_decl);
  gimple_stmt_iterator gsi;
  gcall *stmt1;
  gassign *stmt2;
  tree tree_uid, cur_func, void0;

  if (c_node->only_called_directly_p ())
    return;

  gimple_init_gcov_profiler ();

  /* Insert code:

    stmt1: __gcov_indirect_call_profiler_v2 (profile_id,
					     &current_function_decl)
   */
  gsi = gsi_after_labels (split_edge (single_succ_edge
					 (ENTRY_BLOCK_PTR_FOR_FN (cfun))));

  cur_func = force_gimple_operand_gsi (&gsi,
				       build_addr (current_function_decl),
				       true, NULL_TREE,
				       true, GSI_SAME_STMT);
  tree_uid = build_int_cst
	      (gcov_type_node,
	       cgraph_node::get (current_function_decl)->profile_id);
  stmt1 = gimple_build_call (tree_indirect_call_profiler_fn, 2,
			     tree_uid, cur_func);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);

  /* Set __gcov_indirect_call_callee to 0,
     so that calls from other modules won't get misattributed
     to the last caller of the current callee. */
  void0 = build_int_cst (build_pointer_type (void_type_node), 0);
  stmt2 = gimple_build_assign (ic_void_ptr_var, void0);
  gsi_insert_before (&gsi, stmt2, GSI_SAME_STMT);
}

/* Output instructions as GIMPLE tree at the beginning for each function.
   TAG is the tag of the section for counters, BASE is offset of the
   counter position and GSI is the iterator we place the counter.  */

void
gimple_gen_time_profiler (unsigned tag, unsigned base)
{
  tree type = get_gcov_type ();
  basic_block entry = ENTRY_BLOCK_PTR_FOR_FN (cfun);
  basic_block cond_bb = split_edge (single_succ_edge (entry));
  basic_block update_bb = split_edge (single_succ_edge (cond_bb));
  split_edge (single_succ_edge (update_bb));

  edge true_edge = single_succ_edge (cond_bb);
  true_edge->flags = EDGE_TRUE_VALUE;
  true_edge->probability = PROB_VERY_UNLIKELY;
  edge e
    = make_edge (cond_bb, single_succ_edge (update_bb)->dest, EDGE_FALSE_VALUE);
  e->probability = REG_BR_PROB_BASE - true_edge->probability;

  gimple_stmt_iterator gsi = gsi_start_bb (cond_bb);
  tree original_ref = tree_coverage_counter_ref (tag, base);
  tree ref = force_gimple_operand_gsi (&gsi, original_ref, true, NULL_TREE,
				       true, GSI_SAME_STMT);
  tree one = build_int_cst (type, 1);

  /* Emit: if (counters[0] != 0).  */
  gcond *cond = gimple_build_cond (EQ_EXPR, ref, build_int_cst (type, 0),
				   NULL, NULL);
  gsi_insert_before (&gsi, cond, GSI_NEW_STMT);

  gsi = gsi_start_bb (update_bb);

  /* Emit: counters[0] = ++__gcov_time_profiler_counter.  */
  if (flag_profile_update == PROFILE_UPDATE_ATOMIC)
    {
      tree ptr = make_temp_ssa_name (build_pointer_type (type), NULL,
				     "time_profiler_counter_ptr");
      tree addr = build1 (ADDR_EXPR, TREE_TYPE (ptr),
			  tree_time_profiler_counter);
      gassign *assign = gimple_build_assign (ptr, NOP_EXPR, addr);
      gsi_insert_before (&gsi, assign, GSI_NEW_STMT);
      tree f = builtin_decl_explicit (LONG_LONG_TYPE_SIZE > 32
				      ? BUILT_IN_ATOMIC_ADD_FETCH_8:
				      BUILT_IN_ATOMIC_ADD_FETCH_4);
      gcall *stmt = gimple_build_call (f, 3, ptr, one,
				       build_int_cst (integer_type_node,
						      MEMMODEL_RELAXED));
      tree result_type = TREE_TYPE (TREE_TYPE (f));
      tree tmp = make_temp_ssa_name (result_type, NULL, "time_profile");
      gimple_set_lhs (stmt, tmp);
      gsi_insert_after (&gsi, stmt, GSI_NEW_STMT);
      tmp = make_temp_ssa_name (type, NULL, "time_profile");
      assign = gimple_build_assign (tmp, NOP_EXPR,
				    gimple_call_lhs (stmt));
      gsi_insert_after (&gsi, assign, GSI_NEW_STMT);
      assign = gimple_build_assign (original_ref, tmp);
      gsi_insert_after (&gsi, assign, GSI_NEW_STMT);
    }
  else
    {
      tree tmp = make_temp_ssa_name (type, NULL, "time_profile");
      gassign *assign = gimple_build_assign (tmp, tree_time_profiler_counter);
      gsi_insert_before (&gsi, assign, GSI_NEW_STMT);

      tmp = make_temp_ssa_name (type, NULL, "time_profile");
      assign = gimple_build_assign (tmp, PLUS_EXPR, gimple_assign_lhs (assign),
				    one);
      gsi_insert_after (&gsi, assign, GSI_NEW_STMT);
      assign = gimple_build_assign (original_ref, tmp);
      gsi_insert_after (&gsi, assign, GSI_NEW_STMT);
      assign = gimple_build_assign (tree_time_profiler_counter, tmp);
      gsi_insert_after (&gsi, assign, GSI_NEW_STMT);
    }
}

/* Output instructions as GIMPLE trees to increment the average histogram
   counter.  VALUE is the expression whose value is profiled.  TAG is the
   tag of the section for counters, BASE is offset of the counter position.  */

void
gimple_gen_average_profiler (histogram_value value, unsigned tag, unsigned base)
{
  gimple *stmt = value->hvalue.stmt;
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
  tree ref_ptr = tree_coverage_counter_addr (tag, base);
  gcall *call;
  tree val;

  ref_ptr = force_gimple_operand_gsi (&gsi, ref_ptr,
				      true, NULL_TREE,
				      true, GSI_SAME_STMT);
  val = prepare_instrumented_value (&gsi, value);
  call = gimple_build_call (tree_average_profiler_fn, 2, ref_ptr, val);
  gsi_insert_before (&gsi, call, GSI_NEW_STMT);
}

/* Output instructions as GIMPLE trees to increment the ior histogram
   counter.  VALUE is the expression whose value is profiled.  TAG is the
   tag of the section for counters, BASE is offset of the counter position.  */

void
gimple_gen_ior_profiler (histogram_value value, unsigned tag, unsigned base)
{
  gimple *stmt = value->hvalue.stmt;
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
  tree ref_ptr = tree_coverage_counter_addr (tag, base);
  gcall *call;
  tree val;

  ref_ptr = force_gimple_operand_gsi (&gsi, ref_ptr,
				      true, NULL_TREE, true, GSI_SAME_STMT);
  val = prepare_instrumented_value (&gsi, value);
  call = gimple_build_call (tree_ior_profiler_fn, 2, ref_ptr, val);
  gsi_insert_before (&gsi, call, GSI_NEW_STMT);
}

#ifndef HAVE_sync_compare_and_swapsi
#define HAVE_sync_compare_and_swapsi 0
#endif
#ifndef HAVE_atomic_compare_and_swapsi
#define HAVE_atomic_compare_and_swapsi 0
#endif

#ifndef HAVE_sync_compare_and_swapdi
#define HAVE_sync_compare_and_swapdi 0
#endif
#ifndef HAVE_atomic_compare_and_swapdi
#define HAVE_atomic_compare_and_swapdi 0
#endif

/* Profile all functions in the callgraph.  */

static unsigned int
tree_profiling (void)
{
  struct cgraph_node *node;

  /* Verify whether we can utilize atomic update operations.  */
  bool can_support_atomic = false;
  unsigned HOST_WIDE_INT gcov_type_size
    = tree_to_uhwi (TYPE_SIZE_UNIT (get_gcov_type ()));
  if (gcov_type_size == 4)
    can_support_atomic
      = HAVE_sync_compare_and_swapsi || HAVE_atomic_compare_and_swapsi;
  else if (gcov_type_size == 8)
    can_support_atomic
      = HAVE_sync_compare_and_swapdi || HAVE_atomic_compare_and_swapdi;

  if (flag_profile_update == PROFILE_UPDATE_ATOMIC
      && !can_support_atomic)
    {
      warning (0, "target does not support atomic profile update, "
	       "single mode is selected");
      flag_profile_update = PROFILE_UPDATE_SINGLE;
    }
  else if (flag_profile_update == PROFILE_UPDATE_PREFER_ATOMIC)
    flag_profile_update = can_support_atomic
      ? PROFILE_UPDATE_ATOMIC : PROFILE_UPDATE_SINGLE;

  /* This is a small-ipa pass that gets called only once, from
     cgraphunit.c:ipa_passes().  */
  gcc_assert (symtab->state == IPA_SSA);

  init_node_map (true);

  FOR_EACH_DEFINED_FUNCTION (node)
    {
      if (!gimple_has_body_p (node->decl))
	continue;

      /* Don't profile functions produced for builtin stuff.  */
      if (DECL_SOURCE_LOCATION (node->decl) == BUILTINS_LOCATION)
	continue;

      if (lookup_attribute ("no_profile_instrument_function",
			    DECL_ATTRIBUTES (node->decl)))
	continue;
      /* Do not instrument extern inline functions when testing coverage.
	 While this is not perfectly consistent (early inlined extern inlines
	 will get acocunted), testsuite expects that.  */
      if (DECL_EXTERNAL (node->decl)
	  && flag_test_coverage)
	continue;

      push_cfun (DECL_STRUCT_FUNCTION (node->decl));

      /* Local pure-const may imply need to fixup the cfg.  */
      if (execute_fixup_cfg () & TODO_cleanup_cfg)
	cleanup_tree_cfg ();

      branch_prob ();

      if (! flag_branch_probabilities
	  && flag_profile_values)
	gimple_gen_ic_func_profiler ();

      if (flag_branch_probabilities
	  && flag_profile_values
	  && flag_value_profile_transformations)
	gimple_value_profile_transformations ();

      /* The above could hose dominator info.  Currently there is
	 none coming in, this is a safety valve.  It should be
	 easy to adjust it, if and when there is some.  */
      free_dominance_info (CDI_DOMINATORS);
      free_dominance_info (CDI_POST_DOMINATORS);
      pop_cfun ();
    }

  /* Drop pure/const flags from instrumented functions.  */
  if (profile_arc_flag || flag_test_coverage)
    FOR_EACH_DEFINED_FUNCTION (node)
      {
	if (!gimple_has_body_p (node->decl)
	    || !(!node->clone_of
	    || node->decl != node->clone_of->decl))
	  continue;

	/* Don't profile functions produced for builtin stuff.  */
	if (DECL_SOURCE_LOCATION (node->decl) == BUILTINS_LOCATION)
	  continue;

	node->set_const_flag (false, false);
	node->set_pure_flag (false, false);
      }

  /* Update call statements and rebuild the cgraph.  */
  FOR_EACH_DEFINED_FUNCTION (node)
    {
      basic_block bb;

      if (!gimple_has_body_p (node->decl)
	  || !(!node->clone_of
	  || node->decl != node->clone_of->decl))
	continue;

      /* Don't profile functions produced for builtin stuff.  */
      if (DECL_SOURCE_LOCATION (node->decl) == BUILTINS_LOCATION)
	continue;

      push_cfun (DECL_STRUCT_FUNCTION (node->decl));

      FOR_EACH_BB_FN (bb, cfun)
	{
	  gimple_stmt_iterator gsi;
	  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	    {
	      gimple *stmt = gsi_stmt (gsi);
	      if (is_gimple_call (stmt))
		update_stmt (stmt);
        }
	}

      /* re-merge split blocks.  */
      cleanup_tree_cfg ();
      update_ssa (TODO_update_ssa);

      cgraph_edge::rebuild_edges ();

      pop_cfun ();
    }

  handle_missing_profiles ();

  del_node_map ();
  return 0;
}

namespace {

const pass_data pass_data_ipa_tree_profile =
{
  SIMPLE_IPA_PASS, /* type */
  "profile", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_IPA_PROFILE, /* tv_id */
  0, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  TODO_dump_symtab, /* todo_flags_finish */
};

class pass_ipa_tree_profile : public simple_ipa_opt_pass
{
public:
  pass_ipa_tree_profile (gcc::context *ctxt)
    : simple_ipa_opt_pass (pass_data_ipa_tree_profile, ctxt)
  {}

  /* opt_pass methods: */
  virtual bool gate (function *);
  virtual unsigned int execute (function *) { return tree_profiling (); }

}; // class pass_ipa_tree_profile

bool
pass_ipa_tree_profile::gate (function *)
{
  /* When profile instrumentation, use or test coverage shall be performed.
     But for AutoFDO, this there is no instrumentation, thus this pass is
     diabled.  */
  return (!in_lto_p && !flag_auto_profile
	  && (flag_branch_probabilities || flag_test_coverage
	      || profile_arc_flag));
}

} // anon namespace

simple_ipa_opt_pass *
make_pass_ipa_tree_profile (gcc::context *ctxt)
{
  return new pass_ipa_tree_profile (ctxt);
}

#include "gt-tree-profile.h"
