"""Irreducible blocks of the one-site algebra spanned by the partially transposed permutation
operators Gamma_tau(P_p), p in S4, with the local dimension d as a formal parameter.

For a transpose set tau the 24 diagrams are walled Brauer diagrams with left nodes L = complement
of tau and right nodes R = tau.  The blocks are the cell modules W(k, lam, mu): k = number of arcs,
lam a partition of |L|-k, mu a partition of |R|-k; basis = (top half with k arcs) x (polytabloid basis
of S^lam x S^mu).  rho_r(D; d) and the contravariant form G_r(d) are polynomial matrices in d
(dict degree -> object matrix of Fractions), satisfying
    rho(D1) rho(D2) = d^{loops} rho(D1 D2),      rho(D)^T G = G rho(D*).
"""
from fractions import Fraction
from itertools import combinations, permutations, product
import numpy as np
from diagrams import (PERMS, perm_diagram, transpose_diagram, adjoint_diagram, compose_diagrams,
                      trace_loops, diagram_matrix)
from specht import Specht, partitions

# ---------- polynomial matrices: {deg: object ndarray} ----------


def pm_zero(n, m):
    return {}


def pm_add(A, B):
    C = {k: v.copy() for k, v in A.items()}
    for k, v in B.items():
        C[k] = C[k] + v if k in C else v.copy()
    return {k: v for k, v in C.items() if np.any(v != 0)}


def pm_scale(A, s):
    return {k: v * s for k, v in A.items()} if s != 0 else {}


def pm_shift(A, n):
    return {k + n: v for k, v in A.items()}


def pm_mul(A, B):
    C = {}
    for i, u in A.items():
        for j, v in B.items():
            w = u.dot(v)
            C[i + j] = C[i + j] + w if (i + j) in C else w
    return {k: v for k, v in C.items() if np.any(v != 0)}


def pm_T(A):
    return {k: v.T.copy() for k, v in A.items()}


def pm_eq(A, B):
    keys = set(A) | set(B)
    for k in keys:
        if k in A and k in B:
            if not np.array_equal(A[k], B[k]):
                return False
        elif k in A:
            if np.any(A[k] != 0):
                return False
        else:
            if np.any(B[k] != 0):
                return False
    return True


def pm_eval(A, d, shape):
    M = np.zeros(shape, dtype=object)
    for k, v in A.items():
        M = M + v * Fraction(d) ** k
    return M


def pm_kron(A, B):
    C = {}
    for i, u in A.items():
        for j, v in B.items():
            w = np.kron(u, v)
            C[i + j] = C[i + j] + w if (i + j) in C else w
    return {k: v for k, v in C.items() if np.any(v != 0)}


def pm_maxdeg(A):
    return max(A) if A else 0


def obj_eye(n):
    M = np.zeros((n, n), dtype=object)
    for i in range(n):
        M[i, i] = Fraction(1)
    return M


def obj_zeros(n, m):
    M = np.zeros((n, m), dtype=object)
    M[:] = Fraction(0)
    return M


# ---------- cell modules ----------

class CellBlock:
    def __init__(self, alg, k, lam, mu):
        self.alg = alg
        self.k, self.lam, self.mu = k, tuple(lam), tuple(mu)
        L, R = alg.L, alg.R
        self.SL = Specht(lam)
        self.SR = Specht(mu)
        # top halves: k arcs pairing k left out-vertices with k right out-vertices
        halves = []
        for ls in combinations(L, k):
            for rs in combinations(R, k):
                for pr in permutations(rs):
                    halves.append(frozenset(frozenset({('o', a), ('o', b)}) for a, b in zip(ls, pr)))
        self.halves = sorted(set(halves), key=lambda h: sorted(sorted((x[1], x[0]) for x in pair) for pair in h))
        self.hidx = {h: i for i, h in enumerate(self.halves)}
        self.ds = self.SL.dim * self.SR.dim
        self.dim = len(self.halves) * self.ds
        self.name = (k, self.lam, self.mu)
        # canonical diagrams
        self.canon = {h: self._canonical(h) for h in self.halves}
        self._rho_cache = {}
        self.G = self._gram()

    def free_tops(self, h):
        used = {v[1] for pair in h for v in pair}
        Lf = [a for a in self.alg.L if a not in used]
        Rf = [b for b in self.alg.R if b not in used]
        return Lf, Rf

    def _canonical(self, h):
        L, R, k = self.alg.L, self.alg.R, self.k
        pairs = set(h)
        nL, nR = len(L) - k, len(R) - k
        for i in range(k):
            pairs.add(frozenset({('i', L[nL + i]), ('i', R[nR + i])}))
        Lf, Rf = self.free_tops(h)
        for i, a in enumerate(Lf):
            pairs.add(frozenset({('o', a), ('i', L[i])}))
        for i, b in enumerate(Rf):
            pairs.add(frozenset({('o', b), ('i', R[i])}))
        return frozenset(pairs)

    def _read(self, F):
        """For a diagram F with standard bottom and exactly k top arcs: top half and (sigmaL, sigmaR).
        Returns None if F has more than k top arcs."""
        L, R, k = self.alg.L, self.alg.R, self.k
        nL, nR = len(L) - k, len(R) - k
        top = frozenset(p for p in F if all(v[0] == 'o' for v in p))
        if len(top) != k:
            assert len(top) > k
            return None
        Lf, Rf = self.free_tops(top)
        partner = {}
        for p in F:
            a, b = tuple(p)
            partner[a] = b
            partner[b] = a
        sL = tuple(Lf.index(partner[('i', L[i])][1]) for i in range(nL))
        sR = tuple(Rf.index(partner[('i', R[i])][1]) for i in range(nR))
        for i in range(nL):
            assert partner[('i', L[i])][0] == 'o'
        for i in range(nR):
            assert partner[('i', R[i])][0] == 'o'
        return top, sL, sR

    def rho(self, D):
        """Polynomial matrix of the diagram D on the block."""
        if D in self._rho_cache:
            return self._rho_cache[D]
        M = {}
        n = self.dim
        for h in self.halves:
            F, loops = compose_diagrams(D, self.canon[h])
            rd = self._read(F)
            if rd is None:
                continue
            h2, sL, sR = rd
            blk = np.kron(self.SL.rho(sL), self.SR.rho(sR))
            i0 = self.hidx[h2] * self.ds
            j0 = self.hidx[h] * self.ds
            if loops not in M:
                M[loops] = obj_zeros(n, n)
            M[loops][i0:i0 + self.ds, j0:j0 + self.ds] += blk
        self._rho_cache[D] = M
        return M

    def _gram(self):
        n = self.dim
        G = {}
        Lam = np.kron(self.SL.Lam, self.SR.Lam)
        for h1 in self.halves:
            for h2 in self.halves:
                F, loops = compose_diagrams(adjoint_diagram(self.canon[h1]), self.canon[h2])
                rd = self._read_form(F)
                if rd is None:
                    continue
                sL, sR = rd
                blk = Lam.dot(np.kron(self.SL.rho(sL), self.SR.rho(sR)))
                i0 = self.hidx[h1] * self.ds
                j0 = self.hidx[h2] * self.ds
                if loops not in G:
                    G[loops] = obj_zeros(n, n)
                G[loops][i0:i0 + self.ds, j0:j0 + self.ds] += blk
        return G

    def _read_form(self, F):
        L, R, k = self.alg.L, self.alg.R, self.k
        nL, nR = len(L) - k, len(R) - k
        top = [p for p in F if all(v[0] == 'o' for v in p)]
        if len(top) != k:
            return None
        partner = {}
        for p in F:
            a, b = tuple(p)
            partner[a] = b
            partner[b] = a
        sL, sR = [], []
        for i in range(nL):
            q = partner[('i', L[i])]
            if q[0] != 'o':
                return None
            sL.append(L.index(q[1]))
        for i in range(nR):
            q = partner[('i', R[i])]
            if q[0] != 'o':
                return None
            sR.append(R.index(q[1]))
        return tuple(sL), tuple(sR)


class SiteAlgebra:
    def __init__(self, tau):
        self.tau = frozenset(tau)
        self.L = sorted(set(range(4)) - self.tau)
        self.R = sorted(self.tau)
        self.D = {p: transpose_diagram(perm_diagram(p), self.tau) for p in PERMS}
        self.p_of = {D: p for p, D in self.D.items()}
        assert len(self.p_of) == 24
        self.blocks = []
        for k in range(min(len(self.L), len(self.R)) + 1):
            for lam in partitions(len(self.L) - k):
                for mu in partitions(len(self.R) - k):
                    self.blocks.append(CellBlock(self, k, lam, mu))

    def adjoint_perm(self, p):
        return self.p_of[adjoint_diagram(self.D[p])]

    def structure(self, p, q):
        """D_p D_q = d^loops D_s; returns (s, loops)."""
        F, loops = compose_diagrams(self.D[p], self.D[q])
        return self.p_of[F], loops

    def check(self, verbose=True):
        tot = sum(b.dim ** 2 for b in self.blocks)
        assert tot == 24, tot
        for b in self.blocks:
            for p in PERMS:
                for q in PERMS:
                    s, loops = self.structure(p, q)
                    lhs = pm_mul(b.rho(self.D[p]), b.rho(self.D[q]))
                    rhs = pm_shift(b.rho(self.D[s]), loops)
                    assert pm_eq(lhs, rhs), ('product rule', self.tau, b.name, p, q)
                pstar = self.adjoint_perm(p)
                assert pm_eq(pm_mul(pm_T(b.rho(self.D[p])), b.G), pm_mul(b.G, b.rho(self.D[pstar]))), ('star', self.tau, b.name, p)
            assert pm_eq(b.G, pm_T(b.G))
        if verbose:
            print('tau =', sorted(self.tau), ': blocks', [(b.name, b.dim) for b in self.blocks], 'sum dim^2 =', tot)
        return True


def multiplicities(alg, dvals=(4, 5, 6, 7, 8, 9)):
    """Solve Tr_phys(D) = sum_r m_r(d) tr rho_r(D) for the m_r at several d (rational)."""
    out = {}
    for d in dvals:
        A = np.zeros((24, len(alg.blocks)), dtype=object)
        bvec = np.zeros(24, dtype=object)
        for i, p in enumerate(PERMS):
            bvec[i] = Fraction(d) ** trace_loops(alg.D[p])
            for j, b in enumerate(alg.blocks):
                M = pm_eval(b.rho(alg.D[p]), d, (b.dim, b.dim))
                A[i, j] = sum(M[t, t] for t in range(b.dim))
        from specht import solve_exact
        out[d] = solve_exact(A, bvec)
    return out


if __name__ == '__main__':
    import sys
    TAUS = [(), (0,), (1,), (2,), (3,), (0, 1), (0, 2), (0, 3)]
    for tau in TAUS:
        alg = SiteAlgebra(tau)
        alg.check()
        # degrees
        for b in alg.blocks:
            kr = max(pm_maxdeg(b.rho(alg.D[p])) for p in PERMS)
            gr = pm_maxdeg(b.G)
            print('   block', b.name, 'dim', b.dim, 'k_r', kr, 'g_r', gr,
                  'G leading PD:', np.linalg.eigvalsh(np.array(b.G[gr], dtype=float)).min() > 1e-12)
        mult = multiplicities(alg)
        print('   multiplicities at d=4..9:', {d: [str(x) for x in v] for d, v in mult.items()})
        # numerical cross-check at d=4: spectrum of a random symmetric element
        d = 4
        rng = np.random.default_rng(1)
        y = {p: rng.standard_normal() for p in PERMS}
        ysym = {p: (y[p] + y[alg.adjoint_perm(p)]) / 2 for p in PERMS}
        Yphys = sum(ysym[p] * diagram_matrix(alg.D[p], d) for p in PERMS)
        ev_phys = np.sort(np.linalg.eigvalsh(Yphys))
        ev_blocks = []
        for j, b in enumerate(alg.blocks):
            G = np.array(pm_eval(b.G, d, (b.dim, b.dim)), dtype=float)
            M = sum(ysym[p] * np.array(pm_eval(b.rho(alg.D[p]), d, (b.dim, b.dim)), dtype=float) for p in PERMS)
            B = G @ M
            assert np.allclose(B, B.T), 'B not symmetric'
            w, V = np.linalg.eigh(G)
            Gh = V @ np.diag(np.sqrt(w)) @ V.T
            Ghi = V @ np.diag(1 / np.sqrt(w)) @ V.T
            ev = np.linalg.eigvalsh(Gh @ M @ Ghi)
            m = int(mult[d][j])
            ev_blocks += list(ev) * m
        ev_blocks = np.sort(ev_blocks)
        assert len(ev_blocks) == d ** 4, (len(ev_blocks), d ** 4)
        assert np.allclose(ev_blocks, ev_phys, atol=1e-8), np.abs(ev_blocks - ev_phys).max()
        print('   spectrum of a random symmetric element at d=4 reproduced from the blocks')
