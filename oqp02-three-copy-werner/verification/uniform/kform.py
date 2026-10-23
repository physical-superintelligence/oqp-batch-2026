"""The dyad lift and the four-replica determinant form.

X = s0 u0 v0^dag + s1 u1 v1^dag on H = H1 x H2 x H3,  D_j = u_j v_j^dag.
H_w(i,j) = sum_S w_S <Tr_S D_i, Tr_S D_j>  (<A,B> = Tr A^dag B),  Q_w(X) = s^T H_w s.
Replicas r = (u0, v0, u1, v1) = (0,1,2,3).
K(w) = sum_{S,R} w_S w_R ( x_i P_{d(e_i,f_i)} - x_i P_{c(e_i,f_i)} ),  e_i = [i in S], f_i = [i in R],
d(e,f) = (01)^e (23)^f,   c(e,f) = (03)^e (12)^f (02)(13)   (right to left),
and <r, K(w) r> = det H_w for all four vectors.
A site-triple tensor is a dict {(p1,p2,p3): coefficient}.
"""
from fractions import Fraction
from itertools import product
import numpy as np
from diagrams import PERMS, IDENT, pmul, pinv, cyc

SUBSETS = [frozenset(s) for k in range(4) for s in __import__('itertools').combinations(range(3), k)]


def weights_alpha(alpha):
    return {S: (-alpha) ** len(S) for S in SUBSETS}


def dperm(e, f):
    p = IDENT
    if e:
        p = pmul(cyc((0, 1)), p)
    if f:
        p = pmul(cyc((2, 3)), p)
    return p


def cperm(e, f):
    p = pmul(cyc((0, 2)), cyc((1, 3)))
    if f:
        p = pmul(cyc((1, 2)), p)
    if e:
        p = pmul(cyc((0, 3)), p)
    return p


def tensor_add(T, key, c):
    if c == 0:
        return
    T[key] = T.get(key, 0) + c
    if T[key] == 0:
        del T[key]


def K_of_weights(w):
    """det-form tensor for weights w (dict over SUBSETS)."""
    K = {}
    for S in SUBSETS:
        for R in SUBSETS:
            c = w[S] * w[R]
            if c == 0:
                continue
            tensor_add(K, tuple(dperm(i in S, i in R) for i in range(3)), c)
            tensor_add(K, tuple(cperm(i in S, i in R) for i in range(3)), -c)
    return K


# ---------- numerics ----------

def partial_trace(X, dims, S):
    """Tr_S X for X on H1xH2xH3 (matrix), S subset of {0,1,2}; returns matrix on remaining sites."""
    d1, d2, d3 = dims
    T = X.reshape(d1, d2, d3, d1, d2, d3)
    keep = [i for i in range(3) if i not in S]
    for i in sorted(S, reverse=True):
        T = np.trace(T, axis1=i, axis2=i + T.ndim // 2)
    n = int(np.prod([dims[i] for i in keep])) if keep else 1
    return T.reshape(n, n)


def Q_weights(X, dims, w):
    return sum(w[S] * np.linalg.norm(partial_trace(X, dims, S), 'fro') ** 2 for S in SUBSETS)


def H_matrix(vecs, dims, w):
    u0, v0, u1, v1 = vecs
    D = [np.outer(u0, v0.conj()), np.outer(u1, v1.conj())]
    H = np.zeros((2, 2), dtype=complex)
    for i in range(2):
        for j in range(2):
            H[i, j] = sum(w[S] * np.vdot(partial_trace(D[i], dims, S), partial_trace(D[j], dims, S)) for S in SUBSETS)
    return H


def expectation(vecs, dims, T):
    """<r, T r> for r = u0 x v0 x u1 x v1 and a site-triple tensor T."""
    tens = [v.reshape(dims) for v in vecs]
    r = np.einsum('abc,def,ghi,jkl->abcdefghijkl', *tens)  # axes (j,i) -> 3j+i
    tot = 0
    for (p1, p2, p3), c in T.items():
        ps = (p1, p2, p3)
        axes = [0] * 12
        for i in range(3):
            pi_inv = pinv(ps[i])
            for m in range(4):
                axes[3 * m + i] = 3 * pi_inv[m] + i
        Pr = r.transpose(axes)
        tot += c * np.vdot(r, Pr)
    return tot


if __name__ == '__main__':
    rng = np.random.default_rng(0)
    for dims in [(2, 2, 2), (2, 3, 2), (3, 2, 2)]:
        n = int(np.prod(dims))
        for trial in range(3):
            alpha = rng.uniform(0, 1)
            w = weights_alpha(alpha)
            K = K_of_weights(w)
            vecs = [rng.standard_normal(n) + 1j * rng.standard_normal(n) for _ in range(4)]
            H = H_matrix(vecs, dims, w)
            detH = np.linalg.det(H)
            e = expectation(vecs, dims, K)
            assert abs(detH - e) < 1e-9 * max(1, abs(detH)), (detH, e)
            # Q_w(X) = s^T H s with X = s0 D0 + s1 D1
            s = rng.standard_normal(2)
            X = s[0] * np.outer(vecs[0], vecs[1].conj()) + s[1] * np.outer(vecs[2], vecs[3].conj())
            assert abs(Q_weights(X, dims, w) - (s @ H @ s).real) < 1e-9
            # hermiticity and diagonal positivity bound (1-alpha)^3 |u|^2|v|^2 for alpha in [0,1)
            assert abs(H[0, 1] - np.conj(H[1, 0])) < 1e-9
            assert H[0, 0].real >= (1 - alpha) ** 3 * np.linalg.norm(vecs[0]) ** 2 * np.linalg.norm(vecs[1]) ** 2 - 1e-9
    K = K_of_weights(weights_alpha(Fraction(1, 2)))
    print('det form validated;', len(K), 'monomials in K(1/2)')
