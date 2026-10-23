"""Numerical checks of every identity and inequality in the proof of Theorem B.1 (the all-dimension endpoint bound)
    q(X) >= -N/16 + T/32 + g/8  (eq. (B1)),   q(X) = sum_E (-1/2)^{|E|} ||Tr_E X||^2,  g = (s1 - s2)^2,
for X = U S V^dag of rank <= 2 on H1 x H2 x H3 (unequal dimensions)."""
import numpy as np
from itertools import combinations
import os, sys
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "uniform"))
from kform import partial_trace, SUBSETS

rng = np.random.default_rng(7)
PAULI = [np.eye(2), np.array([[0, 1], [1, 0]]), np.array([[0, -1j], [1j, 0]]), np.array([[1, 0], [0, -1]])]


def q(X, dims, w=None):
    return sum((-0.5) ** len(S) * np.linalg.norm(partial_trace(X, dims, S), 'fro') ** 2 for S in SUBSETS)


def qpol(A, B, dims):
    return sum((-0.5) ** len(S) * np.vdot(partial_trace(A, dims, S), partial_trace(B, dims, S)) for S in SUBSETS)


def tr_all_but(X, dims, i):
    return partial_trace(X, dims, [j for j in range(3) if j != i])


def random_frames(n):
    U = np.linalg.qr(rng.standard_normal((n, 2)) + 1j * rng.standard_normal((n, 2)))[0]
    V = np.linalg.qr(rng.standard_normal((n, 2)) + 1j * rng.standard_normal((n, 2)))[0]
    return U, V


def gap(P):
    ev = np.sort(np.linalg.eigvalsh(P))[::-1]
    return ev[0] - ev[1]


def check_A1(dims):
    """q(P) >= gap(P)^2/8 for PSD rank-2 P, via the stated chain."""
    n = int(np.prod(dims))
    W, _ = random_frames(n)
    lam = rng.uniform(0, 1)
    tau = np.diag([lam, 1 - lam])
    P = W @ tau @ W.conj().T
    st = np.diag(np.sqrt(np.diag(tau)))
    M = {}
    for i in range(3):
        for nu in range(4):
            M[i, nu] = tr_all_but(W @ st @ PAULI[nu] @ st @ W.conj().T, dims, i)
    # (B3) completeness identity: sum_{nu=1..3} ||M_{i nu}||^2 = 2||Tr_i P||^2 - ||Tr_ihat P||^2
    for i in range(3):
        lhs = sum(np.linalg.norm(M[i, nu], 'fro') ** 2 for nu in (1, 2, 3))
        rhs = 2 * np.linalg.norm(partial_trace(P, dims, [i]), 'fro') ** 2 - np.linalg.norm(tr_all_but(P, dims, i), 'fro') ** 2
        assert abs(lhs - rhs) < 1e-9, (lhs, rhs)
    # anticommuting triples bound: sum over a triple of ||M||_1^2 <= 1
    def nuc(A):
        return np.abs(np.linalg.eigvalsh((A + A.conj().T) / 2)).sum()
    for shift in range(3):
        tot = sum(nuc(M[i, 1 + (i + shift) % 3]) ** 2 for i in range(3))
        assert tot <= 1 + 1e-9, tot
    # 2||M||_F^2 <= ||M||_1^2 + (Tr M)^2 and Tr M_{i nu} = (lam-mu) delta_{nu 3}
    for i in range(3):
        for nu in (1, 2, 3):
            A = M[i, nu]
            assert 2 * np.linalg.norm(A, 'fro') ** 2 <= nuc(A) ** 2 + np.trace(A).real ** 2 + 1e-9
            assert abs(np.trace(A) - ((lam - (1 - lam)) if nu == 3 else 0)) < 1e-9
    assert sum(np.linalg.norm(M[i, nu], 'fro') ** 2 for i in range(3) for nu in (1, 2, 3)) <= 3 * np.trace(tau @ tau) + 1e-9
    assert q(P, dims) >= gap(P) ** 2 / 8 - 1e-9
    return True


def check_A2(dims):
    n = int(np.prod(dims))
    U, V = random_frames(n)
    s1, s2 = sorted(rng.uniform(0, 2, 2), reverse=True)
    S = np.diag([s1, s2])
    X = U @ S @ V.conj().T
    N = np.linalg.norm(X, 'fro') ** 2
    T = abs(np.trace(X)) ** 2
    s = s1 + s2
    P, Q = U @ S @ U.conj().T, V @ S @ V.conj().T
    f = np.trace(P @ Q).real
    G = 2 * f - T
    g = 2 * N - s ** 2
    assert abs(g - (s1 - s2) ** 2) < 1e-9
    Bj = [sum(np.linalg.norm(partial_trace(X, dims, S_), 'fro') ** 2 for S_ in SUBSETS if len(S_) == j) for j in range(4)]
    B1, B2 = Bj[1], Bj[2]
    E = q(P, dims) + q(Q, dims)
    h = sum((-0.5) ** len(J) * np.trace(partial_trace(P, dims, J) @ partial_trace(Q, dims, J)).real for J in SUBSETS)
    comp = lambda J: [i for i in range(3) if i not in J]
    c = [sum(np.trace(partial_trace(P, dims, comp(J)) @ partial_trace(Q, dims, comp(J))).real for J in SUBSETS if len(J) == j) for j in range(4)]
    c1, c2 = c[1], c[2]
    # Delta
    st = np.sqrt(S)
    Delta = 0
    for i in range(3):
        for nu in (1, 2, 3):
            D = tr_all_but(U @ st @ PAULI[nu] @ st @ U.conj().T - V @ st @ PAULI[nu] @ st @ V.conj().T, dims, i)
            Delta += np.linalg.norm(D, 'fro') ** 2
    # S_plus: L = Pi (U sqrt S x V sqrt S), Pi = prod_i (I - F_i)/2 on H x H ; Sc = Tr[(I+F_l)/2 L^dag L]
    A = U @ st  # n x 2
    Bm = V @ st
    L = np.kron(A, Bm)  # (n*n) x 4, logical index (a,b)
    d1, d2, d3 = dims
    # swap of site i between the two replicas on H x H
    def swap_site(M, i):
        Mt = M.reshape(d1, d2, d3, d1, d2, d3, 4)
        ax = list(range(7))
        ax[i], ax[3 + i] = ax[3 + i], ax[i]
        return Mt.transpose(ax).reshape(n * n, 4)
    Lp = L.copy()
    for i in range(3):
        Lp = (Lp - swap_site(Lp, i)) / 2
    Fl = np.zeros((4, 4))
    for a in range(2):
        for b in range(2):
            Fl[2 * b + a, 2 * a + b] = 1
    LL = Lp.conj().T @ Lp
    Sc = np.trace((np.eye(4) + Fl) / 2 @ LL).real
    assert Sc >= -1e-12 and Delta >= -1e-12
    # the three expansions (Appendix B, Step 2, relations (1)-(3))
    assert abs(8 * h - (8 * f - 4 * c2 + 2 * c1 - s ** 2)) < 1e-8, '8h'
    assert abs(4 * E + Delta - (8 * N - s ** 2 - 4 * B1 + 2 * c1)) < 1e-8, '4E+Delta'
    assert abs(64 * Sc - 4 * (s ** 2 + N - c1 + c2 - f - B1 + B2 - T)) < 1e-8, '64S'
    # four-phase averaging
    Pz = {z: (U + z * V) @ S @ (U + z * V).conj().T for z in (1, -1, 1j, -1j)}
    assert abs(sum(q(Pz[z], dims) for z in Pz) - (4 * E + 8 * h + 8 * q(X, dims))) < 1e-8
    assert abs(sum(gap(Pz[z]) ** 2 for z in Pz) - (16 * g + 8 * G)) < 1e-8
    # (B4) and (B5)
    e = sum(q(Pz[z], dims) - gap(Pz[z]) ** 2 / 8 for z in Pz)
    assert abs(24 * q(X, dims) - 4 * g + G - (e + Delta + 64 * Sc)) < 1e-8, 'A2'
    assert q(X, dims) >= (4 * g - G) / 24 - 1e-9
    # Hermitian reduction (B6)-(B7): q(Y) >= (2||Y||^2 - ||Y||_1^2)/8 for Re X, Im X; polarised bound
    for Y in ((X + X.conj().T) / 2, (X - X.conj().T) / (2j)):
        ev, W = np.linalg.eigh(Y)
        assert (ev > 1e-9).sum() <= 2 and (ev < -1e-9).sum() <= 2
        Ap = W @ np.diag(np.maximum(ev, 0)) @ W.conj().T
        An = W @ np.diag(np.maximum(-ev, 0)) @ W.conj().T
        u = np.trace(Ap).real * np.trace(An).real
        a = sum(np.trace(partial_trace(Ap, dims, [i]) @ partial_trace(An, dims, [i])).real for i in range(3))
        b = sum(np.trace(tr_all_but(Ap, dims, i) @ tr_all_but(An, dims, i)).real for i in range(3))
        assert b <= u + a + 1e-9
        assert abs(qpol(Ap, An, dims) - (-a / 2 + b / 4 - u / 8)) < 1e-9
        assert q(Y, dims) >= (2 * np.linalg.norm(Y, 'fro') ** 2 - np.abs(ev).sum() ** 2) / 8 - 1e-9
    ReX, ImX = (X + X.conj().T) / 2, (X - X.conj().T) / (2j)
    n1 = lambda Y: np.abs(np.linalg.eigvalsh(Y)).sum()
    assert abs(q(X, dims) - q(ReX, dims) - q(ImX, dims)) < 1e-9
    assert q(X, dims) >= (2 * N - n1(ReX) ** 2 - n1(ImX) ** 2) / 8 - 1e-9
    # Bessel: ||Re X||_1^2 + ||Im X||_1^2 <= 4N - 2f, f = ||sqrt S U^dag V sqrt S||^2
    C = U.conj().T @ V
    Z = st @ C @ st
    assert abs(f - np.linalg.norm(Z, 'fro') ** 2) < 1e-9
    ent = np.linalg.norm(np.imag((C @ S - (C @ S).conj().T) / 2j) if False else (C @ S - (C @ S).conj().T) / 2j, 'fro') ** 2 \
        + np.linalg.norm((S @ C - (S @ C).conj().T) / 2j, 'fro') ** 2 - 2 * np.linalg.norm((Z - Z.conj().T) / 2j, 'fro') ** 2
    assert abs(ent - 0.5 * sum((S[i, i] - S[j, j]) ** 2 * abs(C[i, j]) ** 2 for i in range(2) for j in range(2))) < 1e-9
    assert n1(ReX) ** 2 <= 2 * N - 2 * np.linalg.norm((Z - Z.conj().T) / 2j, 'fro') ** 2 + 1e-9
    assert n1(ReX) ** 2 + n1(ImX) ** 2 <= 4 * N - 2 * f + 1e-9
    assert q(X, dims) >= (G + T - 2 * N) / 8 - 1e-9
    # final
    assert q(X, dims) >= -N / 16 + T / 32 + g / 8 - 1e-9
    return True


if __name__ == '__main__':
    for dims in [(2, 2, 2), (3, 2, 2), (2, 3, 3), (3, 3, 2), (4, 2, 3)]:
        for _ in range(20):
            check_A1(dims)
            check_A2(dims)
    print('all identities and inequalities of the all-dimension bound verified on random instances')
