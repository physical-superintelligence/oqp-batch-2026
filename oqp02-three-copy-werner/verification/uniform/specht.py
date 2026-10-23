"""Rational Specht modules of S_n (n <= 4) in the polytabloid basis, with the invariant form.

A permutation of {0..n-1} is a tuple s with s[j] = s(j); it acts on a tableau entry e by s(e).
Representation matrices rho(s) are rational (Fraction) and satisfy rho(s)^T Lam rho(s) = Lam with
Lam the (rational, symmetric, positive definite) Gram matrix of the polytabloids in tabloid space.
"""
from fractions import Fraction
from itertools import permutations
import numpy as np


def partitions(n):
    if n == 0:
        return [()]
    out = []

    def rec(rem, maxpart, cur):
        if rem == 0:
            out.append(tuple(cur))
            return
        for p in range(min(rem, maxpart), 0, -1):
            rec(rem - p, p, cur + [p])
    rec(n, n, [])
    return out


def standard_tableaux(lam):
    n = sum(lam)
    cells = [(r, c) for r, l in enumerate(lam) for c in range(l)]
    out = []

    def rec(filled, nxt):
        if nxt == n:
            out.append(dict(filled))
            return
        for (r, c) in cells:
            if (r, c) in filled:
                continue
            if c > 0 and (r, c - 1) not in filled:
                continue
            if r > 0 and (r - 1, c) not in filled:
                continue
            filled[(r, c)] = nxt
            rec(filled, nxt + 1)
            del filled[(r, c)]
    rec({}, 0)
    return out  # list of dicts cell -> entry


def sign(p):
    s = 1
    p = list(p)
    for i in range(len(p)):
        while p[i] != i:
            j = p[i]
            p[i], p[j] = p[j], p[i]
            s = -s
    return s


class Specht:
    """Specht module S^lam over Q in the polytabloid basis indexed by standard tableaux."""

    def __init__(self, lam):
        self.lam = tuple(lam)
        self.n = sum(lam)
        n = self.n
        self.tabs = standard_tableaux(lam)
        self.dim = len(self.tabs)
        # tabloid = tuple of frozensets (rows)
        self.rowsets = None
        # polytabloid of a tableau T: sum over column stabilizer sigma of sgn(sigma) {sigma T}
        self.polys = [self._polytabloid(T) for T in self.tabs]
        # choose a basis of tabloids appearing, build coordinate vectors
        keys = sorted({t for poly in self.polys for t in poly}, key=lambda t: [sorted(r) for r in t])
        self.keys = keys
        self.kidx = {t: i for i, t in enumerate(keys)}
        self.E = np.zeros((len(keys), self.dim), dtype=object)
        for j, poly in enumerate(self.polys):
            for t, c in poly.items():
                self.E[self.kidx[t], j] = Fraction(c)
        # Gram matrix (invariant form)
        self.Lam = self.E.T.dot(self.E)
        # pseudo-inverse data for expressing vectors in the polytabloid basis: solve E x = v
        self._cache = {}

    def _tabloid(self, T):
        rows = [frozenset(e for (r, c), e in T.items() if r == i) for i in range(len(self.lam))]
        return tuple(rows)

    def _polytabloid(self, T):
        cols = {}
        for (r, c), e in T.items():
            cols.setdefault(c, []).append(e)
        # column stabilizer: product of permutations within each column
        from itertools import product as iproduct
        colperms = []
        for c in sorted(cols):
            entries = cols[c]
            colperms.append([dict(zip(entries, pe)) for pe in permutations(entries)])
        poly = {}
        for combo in iproduct(*colperms):
            sigma = {}
            for m in combo:
                sigma.update(m)
            sgn = sign(tuple(sigma.get(i, i) for i in range(self.n)))
            T2 = {cell: sigma.get(e, e) for cell, e in T.items()}
            t = self._tabloid(T2)
            poly[t] = poly.get(t, 0) + sgn
        return {t: c for t, c in poly.items() if c != 0}

    def act_tabloid_vector(self, s, v):
        """Apply permutation s to a vector in tabloid coordinates (as dict key->coef)."""
        out = np.zeros(len(self.keys), dtype=object)
        for i, t in enumerate(self.keys):
            if v[i] == 0:
                continue
            t2 = tuple(frozenset(s[e] for e in row) for row in t)
            out[self.kidx[t2]] += v[i]
        return out

    def rho(self, s):
        """Matrix of the permutation s in the polytabloid basis (rational)."""
        s = tuple(s)
        if s in self._cache:
            return self._cache[s]
        M = np.zeros((self.dim, self.dim), dtype=object)
        for j in range(self.dim):
            img = self.act_tabloid_vector(s, self.E[:, j])
            # solve E x = img exactly (E has full column rank)
            x = solve_exact(self.E, img)
            M[:, j] = x
        self._cache[s] = M
        return M


def solve_exact(A, b):
    """Exact rational least-squares-free solve for full-column-rank A (object arrays)."""
    m, n = A.shape
    # Gaussian elimination on [A|b] over Fractions
    M = [[Fraction(A[i, j]) for j in range(n)] + [Fraction(b[i])] for i in range(m)]
    row = 0
    piv = []
    for col in range(n):
        pr = next((r for r in range(row, m) if M[r][col] != 0), None)
        if pr is None:
            continue
        M[row], M[pr] = M[pr], M[row]
        pv = M[row][col]
        M[row] = [v / pv for v in M[row]]
        for r in range(m):
            if r != row and M[r][col] != 0:
                f = M[r][col]
                M[r] = [a - f * c for a, c in zip(M[r], M[row])]
        piv.append(col)
        row += 1
    assert len(piv) == n
    for r in range(row, m):
        assert M[r][n] == 0, 'inconsistent'
    x = np.zeros(n, dtype=object)
    for i, col in enumerate(piv):
        x[col] = M[i][n]
    return x


if __name__ == '__main__':
    for n in range(0, 5):
        tot = 0
        for lam in partitions(n):
            S = Specht(lam)
            tot += S.dim ** 2
            perms = list(permutations(range(n))) if n > 0 else [()]
            for a in perms:
                for b in perms:
                    ab = tuple(a[b[j]] for j in range(n))
                    assert np.array_equal(S.rho(a).dot(S.rho(b)), S.rho(ab))
                assert np.array_equal(S.rho(a).T.dot(S.Lam).dot(S.rho(a)), S.Lam)
            # positive definiteness of Lam (numerically)
            L = np.array(S.Lam, dtype=float)
            assert np.linalg.eigvalsh(L).min() > 0
        assert tot == max(1, __import__("math").factorial(n)) if n > 0 else True
        print('S_%d: Specht modules ok, sum dim^2 = %d' % (n, tot))
