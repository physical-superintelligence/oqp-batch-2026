"""Hand inequalities (valid for every rank-<=2 matrix in every dimension) as weight vectors a over
subsets S of the three sites, Q_a(X) = sum_S a_S ||Tr_S X||^2 >= 0, hence H_a >= 0 on every pair of
dyads and the four-replica tensors
    T_pm(a,a') = H00 H'11 + H11 H'00 +- (H01 H'10 + H10 H'01)  >= 0,
    det H_a = T_-(a,a)/2.
"""
from fractions import Fraction
import numpy as np
from kform import SUBSETS, dperm, cperm, tensor_add, H_matrix, expectation

F = Fraction


def weights(d):
    w = {S: F(0) for S in SUBSETS}
    for k, v in d.items():
        w[frozenset(k)] = F(v)
    return w


def hand_inequalities():
    """Named list of valid weight vectors (all dimensions, rank <= 2)."""
    out = []
    for i in range(3):
        out.append(('one-site %d' % i, weights({(): 1, (i,): F(-1, 2)})))
    for i in range(3):
        j, k = [x for x in range(3) if x != i]
        out.append(('two-site cut %d|%d%d' % (i, j, k), weights({(): 1, (i,): F(-1, 2), (j, k): F(-1, 2), (0, 1, 2): F(1, 4)})))
    for i in range(3):
        for j in range(i + 1, 3):
            out.append(('two-site %d%d spectator' % (i, j), weights({(): 1, (i,): F(-1, 2), (j,): F(-1, 2), (i, j): F(1, 4)})))
    return out


def lemma2_weights():
    """The weight vector a_B of Theorem B.1 of the paper: 17N/8 - B1 + B2/2 - 5T/16 >= (s1-s2)^2/4 in every
    dimension (equivalently q >= -N/16 + T/32 + (s1-s2)^2/8).  The internal name 'lemma2' (also the key
    'det lemma2' of the multiplier mu in certificate_uniform.json) refers to this bound; T_B = det H_{a_B}."""
    return weights({(): F(17, 8), (0,): -1, (1,): -1, (2,): -1, (0, 1): F(1, 2), (0, 2): F(1, 2), (1, 2): F(1, 2), (0, 1, 2): F(-5, 16)})


def T_tensor(a, b, sign):
    T = {}
    for S in SUBSETS:
        for R in SUBSETS:
            c = a[S] * b[R]
            if c == 0:
                continue
            e = tuple(i in S for i in range(3))
            f = tuple(i in R for i in range(3))
            tensor_add(T, tuple(dperm(e[i], f[i]) for i in range(3)), c)
            tensor_add(T, tuple(dperm(f[i], e[i]) for i in range(3)), c)
            tensor_add(T, tuple(cperm(e[i], f[i]) for i in range(3)), sign * c)
            tensor_add(T, tuple(cperm(f[i], e[i]) for i in range(3)), sign * c)
    return T


if __name__ == '__main__':
    from kform import K_of_weights
    rng = np.random.default_rng(3)
    dims = (2, 3, 2)
    n = 12
    hands = hand_inequalities() + [('lemma2', lemma2_weights())]
    for name, a in hands:
        for name2, b in hands:
            Tp = T_tensor(a, b, +1)
            Tm = T_tensor(a, b, -1)
            for _ in range(3):
                vecs = [rng.standard_normal(n) + 1j * rng.standard_normal(n) for _ in range(4)]
                Ha = H_matrix(vecs, dims, {S: float(v) for S, v in a.items()})
                Hb = H_matrix(vecs, dims, {S: float(v) for S, v in b.items()})
                ep = expectation(vecs, dims, Tp)
                em = expectation(vecs, dims, Tm)
                want_p = Ha[0, 0] * Hb[1, 1] + Ha[1, 1] * Hb[0, 0] + Ha[0, 1] * Hb[1, 0] + Ha[1, 0] * Hb[0, 1]
                want_m = Ha[0, 0] * Hb[1, 1] + Ha[1, 1] * Hb[0, 0] - Ha[0, 1] * Hb[1, 0] - Ha[1, 0] * Hb[0, 1]
                assert abs(ep - want_p) < 1e-8 and abs(em - want_m) < 1e-8
                assert ep.real > -1e-9 and em.real > -1e-9, (name, name2, ep, em)
                assert np.linalg.eigvalsh(Ha).min() > -1e-9, (name, 'H not PSD')
        Kd = K_of_weights(a)
        Tm = T_tensor(a, a, -1)
        assert all(abs(Tm.get(k, 0) - 2 * v) == 0 for k, v in Kd.items()) and all(k in Kd for k in Tm)
    print('hand cone tensors validated:', len(hands), 'inequalities')
