//  g++ -O2 -Wall q.cc -lminisat

#include <minisat/simp/SimpSolver.h>
#include <cstdlib>
#include <iostream>

using namespace Minisat;

int p[1<<18];
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

static bool solve(int n)
{
    SimpSolver s;
    Var v[2*l];
    for (int i = 0; i < l && p[i] < n; i++) {
        v[2*i] = s.newVar();
        v[2*i+1] = s.newVar();
        if (!s.addClause(~mkLit(v[2*i]), ~mkLit(v[2*i+1])))
            return false;
    }
    vec<Lit> c[n];
    for (int j = 0; j < l; j++) {
        int q = p[j];
        for (int i = q; i < n; i += q)
            c[i].push(mkLit(v[2*j]));
        for (int i = n-q; i > 0; i -= q)
            c[i].push(mkLit(v[2*j+1]));
    }
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
