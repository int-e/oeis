// Compute Erdős-Woods numbers (cf. https://oeis.org/A059756)
//
// n is an EW number if the primes up to n can be partitioned into two
// sets A and B such that for all m in [1,n-1], either m is divisible
// by a prime in A or (n-m) is divisible by a prime in B. This is easily
// encoded as a SAT problem using two variables per prime.
//
// Author: Bertram Felgenhauer <int-e@gmx.de>
//
// 2016-07-30/31: initial version
//
// to compile (needs MiniSat): g++ -O2 -Wall q.cc -lminisat

// Note: It would be interesting to also cover https://oeis.org/A059757.
// That would require enumerating all solutions and doing some slightly
// tedious CRT computation.

#include <cstdlib>
#include <iostream>
#include <minisat/simp/SimpSolver.h>

using namespace Minisat;

// compute prime numbers (naive)

int p[1<<18]; // good up to 3681131
int l;

static void init_primes(int n)
{
    p[0] = 2;
    l = 1;
    for (int q = 3; q < n; q += 2) {
        int t = 1;
        for (int i = 0; ; i++) {
            if (q % p[i] == 0) {
                t = 0;
                break;
            }
            if (p[i]*p[i] > q)
                break;
        }
        if (t)
            p[l++] = q;
    }
}

// check whether n is an EW number
static bool solve(int n)
{
    SimpSolver s;
    Var v[2*l];
    for (int i = 0; i < l && p[i] < n; i++) {
        // allocate two variables per prime
        v[2*i] = s.newVar();
        v[2*i+1] = s.newVar();
        // assert that at most one of them is set
        if (!s.addClause(~mkLit(v[2*i]), ~mkLit(v[2*i+1])))
            return false;
    }
    // prepare clauses for each m by enumerating multiples (like sieving)
    vec<Lit> c[n];
    for (int j = 0; j < l && p[j] < n; j++) {
        int q = p[j];
        for (int i = q; i < n; i += q)
            c[i].push(mkLit(v[2*j]));
        for (int i = n-q; i > 0; i -= q)
            c[i].push(mkLit(v[2*j+1]));
    }
    // assert clauses and solve
    for (int i = 1; i < n; i++) {
        if (!s.addClause_(c[i]))
            return false;
    }
    return s.solve();
}

int main(int argc, char **argv)
{
    int n = atoi(argv[1]);
    init_primes(n);
    for (int i = 1; i <= n; i++) {
        if (i % 100 == 0)
            std::cerr << i << "/" << n << std::endl;
        if (solve(i))
            std::cout << i << std::endl;
    }
}
