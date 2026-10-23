#!/usr/bin/env python3
"""Exact verification of the dimension-uniform four-replica certificate.

Input: a JSON file with rational data
   alpha0, epsilon, mu (multipliers of the hand tensors), y (orbit values of Y_tau for
   tau in {(), (0,), (0,1), (0,2), (0,3)}).
Everything else (the determinant form K, the hand tensors, the diagram algebras, the cell-module
blocks and their leading terms) is recomputed here in exact rational arithmetic.  Checks:
  (1) K_{alpha0} - sum_j mu_j C_j - sum_tau Y_tau is supported on the ideal monomials;
      Y_tau = Y_tau^* (adjoint-invariant), mu_j >= 0;
  (2) for each tau: the 24 diagrams multiply by the diagram rule (product rule of the blocks),
      the blocks satisfy rho(D)^T G = G rho(D*), sum of squared block orders = 24, the block map
      is injective at d = 5 (hence for all but finitely many d), and the leading Gram matrices
      are positive definite;
  (3) for each of the five sets tau = (), (0,), (0,1), (0,2), (0,3) and each unordered triple of blocks, the
      leading block Bbar(0) satisfies Bbar(0) - eps I > 0 (exact LDL^T with positive pivots); for the three
      relabelled singleton sets (1,),(2,),(3,) (which follow from (0,) by symmetry) strict positivity
      Bbar(0) > 0 is checked directly as well (the margin eps is basis dependent and is not asserted there).
Usage:  python3 -I verify_uniform.py certificate_uniform.json
"""
import sys, os, json, time
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
from itertools import product, permutations
import numpy as np
from diagrams import PERMS, IDENT, pmul, pinv, cyc, compose_diagrams, adjoint_diagram, validate_small_d
from cellmod import SiteAlgebra, pm_maxdeg, pm_eval, obj_zeros
from kform import K_of_weights, weights_alpha
from handcone import hand_inequalities, lemma2_weights, T_tensor

F = Fraction
MONOS = list(product(PERMS, repeat=3))
MIDX = {m: i for i, m in enumerate(MONOS)}
V4 = [IDENT, cyc((0, 1), (2, 3)), cyc((0, 2), (1, 3)), cyc((0, 3), (1, 2))]
S3 = list(permutations(range(3)))
TAUS5 = [(), (0,), (0, 1), (0, 2), (0, 3)]
TAUS8 = [(), (0,), (1,), (2,), (3,), (0, 1), (0, 2), (0, 3)]


def act(m, sigma, g, adj):
    m2 = tuple(m[sigma[i]] for i in range(3))
    m2 = tuple(pmul(pmul(g, p), pinv(g)) for p in m2)
    if adj:
        m2 = tuple(pinv(p) for p in m2)
    return m2


def group(use_v4):
    return [(s, g, a) for s in S3 for g in (V4 if use_v4 else [IDENT]) for a in (False, True)]


def mono_of_str(s):
    return tuple(tuple(int(c) for c in part) for part in s.split('|'))


def str_of_mono(m):
    return '|'.join(''.join(str(c) for c in p) for p in m)


def in_ideal(m):
    return any(all(p[a] == b for p in m) for (a, b) in ((2, 0), (0, 2), (1, 3), (3, 1)))


def expand(yorb, use_v4):
    """Orbit values -> full tensor (dict monomial -> Fraction); checks consistency."""
    G = group(use_v4)
    Y = {}
    for s, v in yorb.items():
        m = mono_of_str(s)
        c = F(v)
        if c == 0:
            continue
        for (sg, g, a) in G:
            m2 = act(m, sg, g, a)
            if m2 in Y:
                assert Y[m2] == c, 'inconsistent orbit data'
            Y[m2] = c
    return Y


def symmetrize(T):
    G = group(True)
    out = {}
    for m, c in T.items():
        for (s, g, a) in G:
            m2 = act(m, s, g, a)
            out[m2] = out.get(m2, F(0)) + F(c) / len(G)
    return {m: c for m, c in out.items() if c != 0}


def hand_tensors():
    hands = hand_inequalities()
    names = [h[0] for h in hands]
    out = {}
    for i in range(len(hands)):
        for j in range(i, len(hands)):
            for sgn in (+1, -1):
                out['T%s(%s,%s)' % ('+' if sgn > 0 else '-', names[i], names[j])] = symmetrize(T_tensor(hands[i][1], hands[j][1], sgn))
    L2 = lemma2_weights()
    out['det lemma2'] = symmetrize(K_of_weights(L2))
    for h in hands:
        for sgn in (+1, -1):
            out['T%s(lemma2,%s)' % ('+' if sgn > 0 else '-', h[0])] = symmetrize(T_tensor(L2, h[1], sgn))
    return out


def relabel(Y, g):
    return {tuple(pmul(pmul(g, p), pinv(g)) for p in m): c for m, c in Y.items()}


def ldl_positive(M, eps):
    """Exact test M - eps I > 0 for a symmetric rational matrix (object array)."""
    n = M.shape[0]
    A = [[F(M[i, j]) - (eps if i == j else 0) for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(i):
            assert A[i][j] == A[j][i], 'not symmetric'
    for k in range(n):
        piv = A[k][k]
        if piv <= 0:
            return False
        for i in range(k + 1, n):
            f = A[i][k] / piv
            if f == 0:
                continue
            row_k = A[k]
            row_i = A[i]
            for j in range(k + 1, n):
                row_i[j] -= f * row_k[j]
    return True


def kron_obj(A, B):
    return np.kron(A, B)


def leading_block_matrices(alg):
    """Per block: (dims, A_r(p) = Gbar_r(0) Rbar_r(D_p; 0) as object arrays), plus checks."""
    out = []
    for b in alg.blocks:
        kr = max(pm_maxdeg(b.rho(alg.D[p])) for p in PERMS)
        gr = pm_maxdeg(b.G)
        G0 = b.G[gr]
        assert ldl_positive(G0, F(0)), 'leading Gram not positive definite'
        A = {}
        for p in PERMS:
            R = b.rho(alg.D[p])
            A[p] = G0.dot(R[kr]) if kr in R else obj_zeros(b.dim, b.dim)
        out.append((b.dim, A, b.name, kr, gr))
    return out


def block_of(Y, A1, A2, A3, n1, n2, n3):
    """sum_m Y[m] A1[m0] x A2[m1] x A3[m2] by nested sums."""
    B = obj_zeros(n1 * n2 * n3, n1 * n2 * n3)
    # group by (p1, p2)
    byp = {}
    for m, c in Y.items():
        byp.setdefault((m[0], m[1]), []).append((m[2], c))
    T2 = {}
    for (p1, p2), lst in byp.items():
        T3 = obj_zeros(n3, n3)
        for p3, c in lst:
            T3 = T3 + A3[p3] * c
        T2[p1] = T2.get(p1, obj_zeros(n2 * n3, n2 * n3)) + kron_obj(A2[p2], T3)
    for p1, M in T2.items():
        B = B + kron_obj(A1[p1], M)
    return B


def rank_at(alg, blocks, d):
    """Rank of the 24 x (sum n_r^2) matrix of block images at integer d (exact)."""
    rows = []
    for p in PERMS:
        row = []
        for b in alg.blocks:
            M = pm_eval(b.rho(alg.D[p]), d, (b.dim, b.dim))
            row += [F(x) for x in M.ravel()]
        rows.append(row)
    # Gaussian elimination
    m, n = len(rows), len(rows[0])
    r = 0
    for col in range(n):
        pr = next((i for i in range(r, m) if rows[i][col] != 0), None)
        if pr is None:
            continue
        rows[r], rows[pr] = rows[pr], rows[r]
        pv = rows[r][col]
        for i in range(m):
            if i != r and rows[i][col] != 0:
                f = rows[i][col] / pv
                rows[i] = [a - f * c for a, c in zip(rows[i], rows[r])]
        r += 1
        if r == m:
            break
    return r


def main(path):
    t0 = time.time()
    cert = json.load(open(path))
    alpha0 = F(cert['alpha0'])
    eps = F(cert['epsilon'])
    assert 0 < alpha0 < F(1, 2) and eps > 0
    mu = {k: F(v) for k, v in cert['mu'].items()}
    assert all(v >= 0 for v in mu.values())
    print('alpha0 =', alpha0, '=', float(alpha0), '; epsilon =', eps, '; hand multipliers:',
          {k: str(v) for k, v in mu.items() if v != 0})
    # (1) identity
    K = K_of_weights(weights_alpha(alpha0))
    HT = hand_tensors()
    Y = {}
    for tau in TAUS5:
        key = str(tau)
        Y[tau] = expand(cert['y'][key], tau != (0,))
    Ysingle = {}
    for g in V4:
        for m, c in relabel(Y[(0,)], g).items():
            Ysingle[m] = Ysingle.get(m, F(0)) + c
    resid = dict(K)
    for name, v in mu.items():
        if v == 0:
            continue
        for m, c in HT[name].items():
            resid[m] = resid.get(m, F(0)) - v * c
    for T in (Y[()], Ysingle, Y[(0, 1)], Y[(0, 2)], Y[(0, 3)]):
        for m, c in T.items():
            resid[m] = resid.get(m, F(0)) - c
    bad = [m for m, c in resid.items() if c != 0 and not in_ideal(m)]
    assert not bad, 'identity fails on %d non-ideal monomials' % len(bad)
    n_ideal = sum(1 for m, c in resid.items() if c != 0)
    for tau in TAUS5:
        for m, c in Y[tau].items():
            assert Y[tau].get(tuple(pinv(p) for p in m), F(0)) == c, 'Y not adjoint-invariant'
    print('(1) coefficient identity holds; ideal term supported on %d monomials; Y_tau = Y_tau^*   [%.0f s]' % (n_ideal, time.time() - t0))
    # (2)+(3) blocks
    validate_small_d()
    print('(2) diagram calculus agrees with the explicit operators on (C^d)^{x4} for d = 2, 3: all 105 diagrams, all 11025 products, traces, adjoints, transposes   [%.0f s]' % (time.time() - t0))
    total_blocks = 0
    for tau in TAUS8:
        alg = SiteAlgebra(tau)
        alg.check(verbose=False)
        blocks = leading_block_matrices(alg)
        rk = rank_at(alg, blocks, 5)
        assert rk == 24, rk
        if tau in TAUS5:
            Yt = Y[tau]
        else:
            g = next(g for g in V4 if g[0] == tau[0])
            Yt = relabel(Y[(0,)], g)
        nb = len(blocks)
        count = 0
        for r1 in range(nb):
            for r2 in range(r1, nb):
                for r3 in range(r2, nb):
                    n1, A1, _, _, _ = blocks[r1]
                    n2, A2, _, _, _ = blocks[r2]
                    n3, A3, _, _, _ = blocks[r3]
                    B = block_of(Yt, A1, A2, A3, n1, n2, n3)
                    margin = eps if tau in TAUS5 else F(0)
                    assert ldl_positive(B, margin), ('block not positive', tau, blocks[r1][2], blocks[r2][2], blocks[r3][2])
                    count += 1
        total_blocks += count
        print('(2)(3) tau = %-7s: algebra checks pass, block map injective at d=5, %d leading blocks %s   [%.0f s]'
              % (str(tau), count, '> eps I' if tau in TAUS5 else '> 0 (relabelled set, strict positivity)', time.time() - t0))
    print('ALL CHECKS PASSED: %d blocks; Q_alpha0(X) >= 0 for every rank-<=2 X in every dimension, alpha0 = %s' % (total_blocks, alpha0))


if __name__ == '__main__':
    main(sys.argv[1])
