/* { dg-options "--coverage -fprofile-conditions -std=c++11" } */
/* { dg-do run { target native } } */

#include <vector>
#include <stdexcept>

class nontrivial_destructor {
public:
    explicit nontrivial_destructor (int v) : val (v) {}
    ~nontrivial_destructor () {}

    int val;
};

int identity (int x) { return x; }
int throws (int) { throw std::runtime_error("exception"); }

/* used for side effects to insert nodes in conditional bodies etc. */
int x = 0;

/* conditionals work in the presence of non-trivial destructors */
void mcdc001a (int a)
{
    nontrivial_destructor v (a);

    if (v.val > 0) /* conditions(2/2) */
        x = v.val;
    else
        x = -v.val;
}

/* non-trivial destructor in-loop temporary */
nontrivial_destructor
mcdc002a (int a, int b) {
    for (int i = 0; i < a; i++) /* conditions(2/2) */
    {
        nontrivial_destructor tmp (a);
        if (tmp.val % b) /* conditions(2/2) */
            return nontrivial_destructor (0);
        x += i;
    } /* conditions(suppress) */
      /* conditions(end) */

    return nontrivial_destructor (a * b);
}

/* conditional in constructor */
void mcdc003a (int a)
{
    class C
    {
    public:
        explicit C (int e) : v (e) {
            if (e) /* conditions(1/2) false(0) */
                v = x - e;
        }
        int v;
    };

    C c (a);
    if (c.v > 2) /* conditions(1/2) true(0) */
        x = c.v + a;
}

/* conditional in destructor */
void mcdc004a (int a)
{
    class C
    {
    public:
        explicit C (int e) : v (e) {}
        ~C () {
            if (v) /* conditions(2/2) */
                x = 2 * v;
        }
        int v;
    };

    C c (a);
    x = 1; // arbitrary action between ctor+dtor
}

/* conditional in try */
void mcdc005a (int a) {
    try {
        if (a) /* conditions(1/2) true(0) */
            x = 2 * identity (a);
        else
            x = 1;
    } catch (...) {
        x = 0;
    }
}

/* conditional in catch */
void mcdc006a (int a) {
    try {
        throws (a);
    } catch (std::exception&) {
        if (a) /* conditions(1/2) false(0) */
            x = identity (a);
        else
            x = 0;
    }
}

int
main (void)
{
    mcdc001a (0);
    mcdc001a (1);

    mcdc002a (1, 1);
    mcdc002a (1, 2);

    mcdc003a (1);

    mcdc004a (0);
    mcdc004a (1);

    mcdc005a (0);

    mcdc006a (1);
}

/* { dg-final { run-gcov conditions { --conditions gcov-18.C } } } */
