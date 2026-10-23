"""Symmetry-reduced data for the dimension-uniform certificate SDP.

Certificate:  K_alpha = sum_{tau in T} Y_tau + E + sum_j mu_j C_j,
  T = {∅, {0},{1},{2},{3}, {0,1},{0,2},{0,3}},  Y_{{j}} = g_j Y_{{0}} g_j^{-1} (g_j in V4),
  Gamma_tau(Y_tau) >= 0 for all sufficiently large d  <=  leading blocks B_{tau,r}(0) > 0,
  E supported on the ideal monomials (vanishing on orthonormal frames), C_j hand-cone tensors.
"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..'))
from fractions import Fraction
from itertools import product, permutations
import numpy as np
import scipy.sparse as sp
from diagrams import PERMS, IDENT, pmul, pinv, cyc
from cellmod import SiteAlgebra, pm_maxdeg
from kform import K_of_weights, weights_alpha, SUBSETS
from handcone import hand_inequalities, lemma2_weights, T_tensor

MONOS = list(product(PERMS, repeat=3))
MIDX = {m: i for i, m in enumerate(MONOS)}
V4 = [IDENT, cyc((0, 1), (2, 3)), cyc((0, 2), (1, 3)), cyc((0, 3), (1, 2))]
S3 = list(permutations(range(3)))
TAUS5 = [(), (0,), (0, 1), (0, 2), (0, 3)]


def act(m, sigma, g, adj):
    m2 = tuple(m[sigma[i]] for i in range(3))
    m2 = tuple(pmul(pmul(g, p), pinv(g)) for p in m2)
    if adj:
        m2 = tuple(pinv(p) for p in m2)
    return m2


def group_elements(use_v4):
    return [(s, g, a) for s in S3 for g in (V4 if use_v4 else [IDENT]) for a in (False, True)]


def orbits(use_v4):
    G = group_elements(use_v4)
    orb = [-1] * len(MONOS)
    reps = []
    for i, m in enumerate(MONOS):
        if orb[i] >= 0:
            continue
        k = len(reps)
        reps.append(m)
        for (s, g, a) in G:
            orb[MIDX[act(m, s, g, a)]] = k
    return np.array(orb), reps


def in_ideal(m):
    return any(all(p[a] == b for p in m) for (a, b) in ((2, 0), (0, 2), (1, 3), (3, 1)))


IDEAL = np.array([in_ideal(m) for m in MONOS])


def symmetrize(T):
    """Average a tensor over S3 x V4 x adj."""
    G = group_elements(True)
    out = {}
    for m, c in T.items():
        for (s, g, a) in G:
            m2 = act(m, s, g, a)
            out[m2] = out.get(m2, 0) + Fraction(c) / len(G)
    return {m: c for m, c in out.items() if c != 0}


def tensor_vec(T):
    v = np.zeros(len(MONOS))
    for m, c in T.items():
        v[MIDX[m]] = float(c)
    return v


class SiteBlocks:
    """Leading-order one-site block matrices A_r(p) = Gbar_r(0) Rbar_r(D_p;0) for a transpose set."""

    def __init__(self, tau):
        self.tau = tau
        self.alg = SiteAlgebra(tau)
        self.A = []   # per block: array (24, n, n) float
        self.dims = []
        self.names = []
        self.kg = []
        for b in self.alg.blocks:
            kr = max(pm_maxdeg(b.rho(self.alg.D[p])) for p in PERMS)
            gr = pm_maxdeg(b.G)
            G0 = np.array(b.G[gr], dtype=float)
            arr = np.zeros((24, b.dim, b.dim))
            for i, p in enumerate(PERMS):
                R = b.rho(self.alg.D[p])
                if kr in R:
                    arr[i] = G0 @ np.array(R[kr], dtype=float)
            self.A.append(arr)
            self.dims.append(b.dim)
            self.names.append(b.name)
            self.kg.append((kr, gr))


def block_maps(sb, orb, n_orb):
    """For each unordered triple of blocks, the dense map (n^2, n_orb) from orbit variables to
    the vectorized block matrix."""
    nb = len(sb.A)
    PIDX = {p: i for i, p in enumerate(PERMS)}
    maps = []
    triples = [(a, b, c) for a in range(nb) for b in range(a, nb) for c in range(b, nb)]
    for (r1, r2, r3) in triples:
        n = sb.dims[r1] * sb.dims[r2] * sb.dims[r3]
        M = np.zeros((n * n, n_orb))
        A1, A2, A3 = sb.A[r1], sb.A[r2], sb.A[r3]
        for mi, m in enumerate(MONOS):
            kr = np.kron(np.kron(A1[PIDX[m[0]]], A2[PIDX[m[1]]]), A3[PIDX[m[2]]])
            if not kr.any():
                continue
            M[:, orb[mi]] += kr.ravel()
        maps.append(((r1, r2, r3), n, M))
    return maps


def build(verbose=True):
    orb_full, reps_full = orbits(True)
    orb_0, reps_0 = orbits(False)
    data = {'orb_full': orb_full, 'reps_full': reps_full, 'orb_0': orb_0, 'reps_0': reps_0}
    if verbose:
        print('orbits: full', len(reps_full), ' singleton', len(reps_0), '; ideal monomials', IDEAL.sum(),
              'in', len({orb_full[i] for i in range(len(MONOS)) if IDEAL[i]}), 'orbits')
    data['blocks'] = {}
    for tau in TAUS5:
        sb = SiteBlocks(tau)
        orb = orb_0 if tau == (0,) else orb_full
        n_orb = len(reps_0) if tau == (0,) else len(reps_full)
        maps = block_maps(sb, orb, n_orb)
        data['blocks'][tau] = ({'dims': sb.dims, 'names': sb.names, 'kg': sb.kg}, maps)
        if verbose:
            print('tau', tau, ': blocks', len(maps), 'max order', max(n for _, n, _ in maps),
                  'degrees', sb.kg)
    # V4-symmetrization matrix for the singleton family: Yfull[m] = sum_g Y0[g^-1 m]
    rows, cols = [], []
    for mi, m in enumerate(MONOS):
        for g in V4:
            rows.append(mi)
            cols.append(orb_0[MIDX[act(m, IDENT, g, False)]])
    data['S_single'] = sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(len(MONOS), len(reps_0)))
    rows, cols = [], []
    for mi in range(len(MONOS)):
        rows.append(mi)
        cols.append(orb_full[mi])
    data['S_full'] = sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(len(MONOS), len(reps_full)))
    # hand-cone auxiliary tensors (symmetrized)
    hands = hand_inequalities()
    aux = []
    names = [h[0] for h in hands]
    for i in range(len(hands)):
        for j in range(i, len(hands)):
            for sgn in (+1, -1):
                aux.append(('T%s(%s,%s)' % ('+' if sgn > 0 else '-', names[i], names[j]),
                            symmetrize(T_tensor(hands[i][1], hands[j][1], sgn))))
    L2 = lemma2_weights()
    aux.append(('det lemma2', symmetrize(K_of_weights(L2))))
    for h in hands:
        for sgn in (+1, -1):
            aux.append(('T%s(lemma2,%s)' % ('+' if sgn > 0 else '-', h[0]), symmetrize(T_tensor(L2, h[1], sgn))))
    data['aux'] = aux
    # dedupe aux tensors (symmetrization identifies many)
    seen = {}
    uniq = []
    for name, T in aux:
        key = tuple(sorted((MIDX[m], c) for m, c in T.items()))
        if key in seen:
            continue
        seen[key] = name
        uniq.append((name, T))
    data['aux'] = uniq
    if verbose:
        print('auxiliary tensors:', len(aux), '->', len(uniq), 'distinct after symmetrization')
    return data


if __name__ == '__main__':
    import pickle, time
    t0 = time.time()
    data = build()
    # K invariance check
    K = K_of_weights(weights_alpha(Fraction(9, 20)))
    Ks = symmetrize(K)
    assert all(abs(Ks.get(m, 0) - K.get(m, 0)) == 0 for m in set(K) | set(Ks)), 'K not symmetric'
    print('K is invariant under S3 x V4 x adjoint; built in %.1f s' % (time.time() - t0))
    with open('sdp_data.pkl', 'wb') as f:
        pickle.dump(data, f)
