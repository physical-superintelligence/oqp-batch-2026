#!/usr/bin/env python3
"""Reproducible numerical evidence for Conjecture 4.4 (Remark 4.5(a),(b)) of
"Three copies of the Werner state in dimensions three and four: the sharp curve and its minimisers".

(a) Random-start minimisation of f(X,Y) = q(XY^dag)/||XY^dag||^2 over X,Y in C^{d^3 x 2} with L-BFGS-B and the
    analytic gradient; every converged zero is classified into family I, II or III by its local supports and an
    explicit comparison with the family's normal form.  Unconverged runs are reported.
(b) Nullity of the Hessian of f at one sampled point of each family (central differences of the analytic gradient),
    compared with the family dimension plus the 10 directions along which f is constant
    (8 from (X,Y) -> (XR, Y R^{-dag}), R in GL(2,C), and 2 from the complex rescaling of C).

usage:  python3 -I zero_census.py d n_starts [seed]        the paper's counts:  zero_census.py 3 500 0  /  zero_census.py 4 200 0
"""
import sys, time, itertools
import numpy as np
from scipy.optimize import minimize

d = int(sys.argv[1]); NSTART = int(sys.argv[2]); SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 0
D = d ** 3
rng = np.random.default_rng(SEED)
SITES = [(), (0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2)]


def ptrace_tensor(T, S):
    """partial trace of the tensor T (shape (d,)*6, index order r1 r2 r3 c1 c2 c3) over the sites in S, result as tensor
    on the remaining sites (rows then columns)."""
    for s in sorted(S, reverse=True):
        T = np.trace(T, axis1=s, axis2=s + T.ndim // 2)
    return T


def embed_identity(T, S):
    """T is a tensor on the sites not in S (rows then columns); return T (x) I_S as a full (d,)*6 tensor."""
    rest = [i for i in range(3) if i not in S]
    k = len(rest)
    out = T
    # insert identity factors: build full tensor by einsum with delta on S sites
    full = np.zeros((d,) * 6, dtype=complex)
    idx = {}
    # iterate over index positions: build with explicit loops via einsum string
    letters = 'abcdef'
    rows = ['' for _ in range(3)]; cols = ['' for _ in range(3)]
    sub_in = ''
    for i in rest:
        rows[i] = letters[i]
    for i in rest:
        cols[i] = letters[3 + i]
    sub_in = ''.join(rows[i] for i in rest) + ''.join(cols[i] for i in rest)
    deltas = []
    delta_subs = []
    for s in S:
        rows[s] = letters[s]; cols[s] = letters[3 + s]
        deltas.append(np.eye(d)); delta_subs.append(letters[s] + letters[3 + s])
    out_sub = ''.join(rows) + ''.join(cols)
    expr = ','.join([sub_in] + delta_subs) + '->' + out_sub
    return np.einsum(expr, T, *deltas)


def q_and_L(C):
    """q(C) and L(C) = sum_S (-1/2)^|S| Tr_S C (x) I_S, so that q = <C, L(C)>."""
    T = C.reshape((d,) * 6)
    L = np.zeros_like(T)
    for S in SITES:
        TS = ptrace_tensor(T, S)
        L += (-0.5) ** len(S) * embed_identity(TS, S)
    L = L.reshape(D, D)
    q = np.vdot(C, L).real
    return q, L


def unpack(p):
    n = D * 2
    X = (p[:n] + 1j * p[n:2 * n]).reshape(D, 2)
    Y = (p[2 * n:3 * n] + 1j * p[3 * n:]).reshape(D, 2)
    return X, Y


def pack(X, Y):
    return np.concatenate([X.real.ravel(), X.imag.ravel(), Y.real.ravel(), Y.imag.ravel()])


def f_and_grad(p):
    X, Y = unpack(p)
    C = X @ Y.conj().T
    N = np.vdot(C, C).real
    q, L = q_and_L(C)
    f = q / N
    dfdCbar = (L * N - q * C) / N ** 2          # Wirtinger derivative d f / d conj(C)
    gX = dfdCbar @ Y                              # d f / d conj(X)
    gY = dfdCbar.conj().T @ X                     # d f / d conj(Y)
    g = np.concatenate([2 * gX.real.ravel(), 2 * gX.imag.ravel(), 2 * gY.real.ravel(), 2 * gY.imag.ravel()])
    return f, g


# ---------------------------------------------------------------- family normal forms
sgm = np.array([[0, 1], [-1, 0]])


def kron(*a):
    o = np.array([[1.0 + 0j]])
    for x in a:
        o = np.kron(o, x)
    return o


def beta(x, y):
    r = int(round(np.log2(len(x))))
    Xi = kron(*([sgm] * r)).real
    th = lambda psi: Xi @ psi.conj()
    return (np.outer(x, th(y).conj()) - np.outer(y, th(x).conj())) / np.sqrt(2)


def local_support(Xb, i):
    """orthonormal basis of the site-i local support of the column space of Xb (D x k), as a d x r matrix"""
    T = Xb.reshape(d, d, d, -1)
    M = np.moveaxis(T, i, 0).reshape(d, -1)
    U, s, _ = np.linalg.svd(M, full_matrices=False)
    r = int(np.sum(s > 1e-2 * s[0]))
    return U[:, :r]


def prop_resid(A, B):
    """relative residual of A being proportional to B"""
    c = np.vdot(B, A) / np.vdot(B, B)
    return np.linalg.norm(A - c * B) / np.linalg.norm(A)


def classify(C):
    """return (family, detail) for a (near-)zero C of rank <= 2, or ('other', detail)"""
    U, s, Vh = np.linalg.svd(C)
    Xb = U[:, :2]; Yb = Vh[:2, :].conj().T          # range and corange bases
    sup_r = [local_support(Xb, i) for i in range(3)]
    sup_c = [local_support(Yb, i) for i in range(3)]
    rr = [S.shape[1] for S in sup_r]; rc = [S.shape[1] for S in sup_c]
    # same local supports?
    same = [rr[i] == rc[i] and np.linalg.norm(sup_r[i] @ sup_r[i].conj().T - sup_c[i] @ sup_c[i].conj().T) < 1e-3 for i in range(3)]
    # family I: some site i with operator-Schmidt rank 1 across i | rest, site factor ~ rank-2 projector, rest rank one
    for i in range(3):
        T = C.reshape((d,) * 6)
        perm = [i, 3 + i] + [j for j in range(3) if j != i] + [3 + j for j in range(3) if j != i]
        M = np.transpose(T, perm).reshape(d * d, -1)
        u, sv, vh = np.linalg.svd(M, full_matrices=False)
        if sv[1] < 1e-2 * sv[0]:
            A = u[:, 0].reshape(d, d) * sv[0]; B = vh[0, :].reshape(d * d, d * d)
            # A proportional to a rank-2 orthogonal projector?
            A = A / np.linalg.norm(A)
            ev = np.linalg.eigvals(A)
            evs = np.sort(np.abs(ev))[::-1]
            herm = np.linalg.norm(A @ A.conj().T - A.conj().T @ A) < 1e-2
            rank2proj = herm and evs[1] > 1e-1 and (len(evs) < 3 or evs[2] < 1e-2) and abs(evs[0] - evs[1]) < 1e-2
            rankB = int(np.sum(np.linalg.svd(B, compute_uv=False) > 1e-2 * np.linalg.norm(B)))
            if rank2proj and rankB == 1:
                return 'I', f'thin site {i+1}'
    # family II: one site with one-dimensional supports; the other two sites (2,2) with equal supports
    ones = [i for i in range(3) if rr[i] == 1 and rc[i] == 1]
    if len(ones) == 1:
        i0 = ones[0]; others = [j for j in range(3) if j != i0]
        if all(rr[j] == 2 and same[j] for j in others):
            V = [sup_r[j] for j in range(3)]
            V[i0] = sup_r[i0]  # d x 1
            Vtot = kron(*V)                    # D x 4
            Wtot = kron(*[sup_r[j] if j != i0 else sup_c[i0] for j in range(3)])   # same bases on the binary sites
            K = Vtot.conj().T @ C @ Wtot       # 4 x 4 on the two binary sites (the rank-one site is a scalar)
            if np.linalg.norm(Vtot @ K @ Wtot.conj().T - C) < 1e-2 * np.linalg.norm(C):
                u2, s2, vh2 = np.linalg.svd(K)
                res = prop_resid(K, beta(u2[:, 0], u2[:, 1]))
                if res < 1e-2:
                    return 'II', f'rank-one site {i0+1}, residual {res:.1e}'
    # family III: all sites (2,2) with equal supports; compression proportional to beta(x,y)
    if all(rr[i] == 2 and same[i] for i in range(3)):
        Vtot = kron(*sup_r)
        K = Vtot.conj().T @ C @ Vtot
        if np.linalg.norm(Vtot @ K @ Vtot.conj().T - C) < 1e-2 * np.linalg.norm(C):
            u3, s3, vh3 = np.linalg.svd(K)
            res = prop_resid(K, beta(u3[:, 0], u3[:, 1]))
            if res < 1e-2:
                return 'III', f'residual {res:.1e}'
    return 'other', f'local ranks range {rr} corange {rc}'


# ---------------------------------------------------------------- (a) random-start census
def random_start():
    X = rng.normal(size=(D, 2)) + 1j * rng.normal(size=(D, 2))
    Y = rng.normal(size=(D, 2)) + 1j * rng.normal(size=(D, 2))
    return pack(X, Y)


ZERO_TOL = 1e-10
counts = {'I': 0, 'II': 0, 'III': 0, 'other': 0, 'unconverged': 0}
details = []
t0 = time.time()
for k in range(NSTART):
    p0 = random_start()
    res = minimize(f_and_grad, p0, jac=True, method='L-BFGS-B', options={'maxiter': 20000, 'gtol': 1e-12, 'ftol': 1e-16})
    res = minimize(f_and_grad, res.x, jac=True, method='L-BFGS-B', options={'maxiter': 20000, 'gtol': 1e-14, 'ftol': 1e-18})  # polish
    X, Y = unpack(res.x); C = X @ Y.conj().T; C = C / np.linalg.norm(C)
    fval = res.fun
    if fval > ZERO_TOL:
        counts['unconverged'] += 1; details.append((k, 'unconverged', f'f = {fval:.2e}, iterations {res.nit}')); continue
    fam, det = classify(C)
    counts[fam] += 1; details.append((k, fam, det + f', f = {fval:.1e}'))
print(f"d = {d}: {NSTART} random starts (seed {SEED}), initial X,Y with i.i.d. standard complex Gaussian entries,")
print(f"L-BFGS-B with analytic gradient (maxiter 20000, gtol 1e-12); a run counts as a zero if f < {ZERO_TOL:.0e}.")
print("family membership: local supports of range and corange at each site + proportionality to the family's normal form (relative residual < 1e-2; near non-generic family members the minimiser stops at distances up to 1e-3 from the exact zero, which is why the tolerance is loose; a matrix outside the families has residual of order one).")
print("counts:", counts, f"  ({time.time()-t0:.0f} s)")
for k, fam, det in details:
    print(f"  start {k:3d}: {fam:12s} {det}")

# ---------------------------------------------------------------- (b) Hessian nullities at sampled family points
def hessian_nullity(X, Y, label):
    p = pack(X, Y); n = len(p); h = 1e-4
    H = np.zeros((n, n))
    for i in range(n):
        e = np.zeros(n); e[i] = h
        H[:, i] = (f_and_grad(p + e)[1] - f_and_grad(p - e)[1]) / (2 * h)
    H = (H + H.T) / 2
    w = np.linalg.eigvalsh(H)
    wmax = w[-1]
    null = int(np.sum(np.abs(w) < 1e-6 * wmax))
    gap = (np.abs(w)[np.abs(w) >= 1e-6 * wmax].min() / wmax) if null < n else 0
    print(f"  {label}: Hessian nullity {null} (next eigenvalue / largest = {gap:.1e}); f = {f_and_grad(p)[0]:.1e}")
    return null


def rand_unit(n):
    v = rng.normal(size=n) + 1j * rng.normal(size=n); return v / np.linalg.norm(v)


def rand_isometry(n, k):
    return np.linalg.qr(rng.normal(size=(n, k)) + 1j * rng.normal(size=(n, k)))[0]


def factors(C):
    U, s, Vh = np.linalg.svd(C); return U[:, :2] * s[:2], Vh[:2, :].conj().T


print(f"Hessian of f at one sampled point of each family (d = {d}); family dimensions + 10 should be: "
      f"I {4*(d-2)+4*(d*d-1)+10}, II {4*(d-1)+8*(d-2)+8+10}, III {12*(d-2)+24+10}")
E = rand_isometry(d, 2); PE = E @ E.conj().T
CI = np.kron(PE, np.outer(rand_unit(d * d), rand_unit(d * d).conj())) / np.sqrt(2)
Vs = [rand_isometry(d, 2) for _ in range(3)]
i2 = rand_isometry(4, 2); CII = np.kron(np.outer(rand_unit(d), rand_unit(d).conj()), kron(Vs[1], Vs[2]) @ beta(i2[:, 0], i2[:, 1]) @ kron(Vs[1], Vs[2]).conj().T)
i3 = rand_isometry(8, 2); CIII = kron(*Vs) @ beta(i3[:, 0], i3[:, 1]) @ kron(*Vs).conj().T
for lab, Cf in (('family I', CI), ('family II', CII), ('family III', CIII)):
    X, Y = factors(Cf)
    hessian_nullity(X, Y, lab)
