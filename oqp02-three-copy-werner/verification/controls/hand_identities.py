#!/usr/bin/env python3
"""Re-checks of the hand-proved identities of the paper (sanity checks, not proofs). Numbering refers to
"Three copies of the Werner state in dimensions three and four: the sharp curve and its minimisers".

  1. Prop. 3.1, the continuation identity  q_alpha - (1-2a)(1-a)^2 N = (4a(1+a)/3) q + a(1-2a)(2/3-a) R + 2a(1-2a) S   (symbolic)
  2. Thm. 1.2, the values (N,A,B,T) = (1,4,5,2) of the sharp family and q_alpha = (1-2a)(1-a)^2 on it   (symbolic + numeric)
  3. Prop. 2.1, the matrix form <vec C, (rho_alpha^Gamma)^{x3} vec C> = q_alpha(C) / [d(d-alpha)]^3   (numeric, d=3)
  4. Appendix A, the two-site identities (A1), (A2) and the sum of squares (A3) on random balanced 3x4 factors   (numeric)
  5. Prop. 4.2(a), the three zero families I, II, III are zeros with both singular values 2^{-1/2}   (numeric, d=3)
  6. Lemma 2.4, q_alpha multiplies over tensor factors and is invariant under local isometries   (numeric)
  7. Remark 3.2(a), the convex decomposition rho_alpha = lam rho_{1/2} + (1-lam) I/d^2 with 0 <= lam <= 1   (numeric)
  8. Remark 4.3, parity of the spin flip: beta^2 = (Tr beta/2) beta for odd r, Tr beta = 0 for even r   (numeric)

Run:  python3 hand_identities.py      (needs numpy, scipy, sympy; about 20 s)
"""
import itertools, sys
import numpy as np
import sympy as sp
from scipy.optimize import minimize

rng = np.random.default_rng(2026)
ok = True
def report(name, cond, detail=""):
    global ok
    ok = ok and bool(cond)
    print(f"[{'ok' if cond else 'FAIL'}] {name} {detail}")

# ---------- helpers ----------
def kron(*ops):
    out = np.array([[1.0+0j]])
    for o in ops: out = np.kron(out, o)
    return out

def ptrace(C, dims, S):
    """unnormalised partial trace over the sites in S (0-indexed) of C on tensor product with local dims"""
    n = len(dims); T = C.reshape(list(dims) * 2)
    axes_out = list(range(n)); axes_in = list(range(n, 2 * n))
    for s in sorted(S, reverse=True):
        a, b = axes_out[s], axes_in[s]
        T = np.trace(T, axis1=a, axis2=b)
        axes_out = [x - (x > a) - (x > b) for x in axes_out if x != a]
        axes_in = [x - (x > a) - (x > b) for x in axes_in if x != b]
    k = len(axes_out)
    return T.reshape(int(np.prod([dims[i] for i in range(n) if i not in S])), -1) if k else np.array(T).reshape(1, 1)

def q_alpha(C, dims, alpha):
    n = len(dims); tot = 0.0
    for r in range(n + 1):
        for S in itertools.combinations(range(n), r):
            tot += (-alpha) ** r * np.linalg.norm(ptrace(C, dims, list(S))) ** 2
    return float(np.real(tot))

def NABT(C, dims):
    N = np.linalg.norm(C) ** 2
    A = sum(np.linalg.norm(ptrace(C, dims, [i])) ** 2 for i in range(3))
    B = sum(np.linalg.norm(ptrace(C, dims, list(S))) ** 2 for S in itertools.combinations(range(3), 2))
    T = abs(np.trace(C)) ** 2
    return N, A, B, T

# ---------- 1. continuation identity (symbolic) ----------
a, N, A, B, T = sp.symbols('a N A B T')
q_a = N - a * A + a ** 2 * B - a ** 3 * T
q = q_a.subs(a, sp.Rational(1, 2))
R = N - T / 2
S = N - (A + B) / 6 + T / 4
f = (1 - 2 * a) * (1 - a) ** 2
rhs = sp.Rational(4, 3) * a * (1 + a) * q + a * (1 - 2 * a) * (sp.Rational(2, 3) - a) * R + 2 * a * (1 - 2 * a) * S
report("Prop. 3.1 continuation identity (symbolic)", sp.simplify(sp.expand(q_a - f * N - rhs)) == 0)

# ---------- 2. sharp family ----------
report("Thm. 1.2 sharp value (1-2a)(1-a)^2 of 2^{-1/2}P_E x |u><u| x |v><v| (symbolic)", sp.simplify(sp.expand(q_a.subs({N: 1, A: 4, B: 5, T: 2}) - f)) == 0)
d = 3
E = np.linalg.qr(rng.normal(size=(d, 2)) + 1j * rng.normal(size=(d, 2)))[0]; PE = E @ E.conj().T
u = rng.normal(size=d) + 1j * rng.normal(size=d); u /= np.linalg.norm(u)
v = rng.normal(size=d) + 1j * rng.normal(size=d); v /= np.linalg.norm(v)
Cstar = kron(PE, np.outer(u, u.conj()), np.outer(v, v.conj())) / np.sqrt(2)
nabt = NABT(Cstar, [d] * 3)
report("sharp family (N,A,B,T)=(1,4,5,2) (numeric)", np.allclose(nabt, (1, 4, 5, 2), atol=1e-12), f"{np.round(nabt,12)}")
alphas = [0.1, 0.3, 0.45]
report("sharp family q_alpha = (1-2a)(1-a)^2 (numeric)", all(abs(q_alpha(Cstar, [d]*3, al) - (1-2*al)*(1-al)**2) < 1e-12 for al in alphas))

# ---------- 3. matrix form ----------
def swap(d):
    F = np.zeros((d * d, d * d))
    for i in range(d):
        for j in range(d): F[i * d + j, j * d + i] = 1
    return F
def site_perm_vec(C, d):
    """vec C grouped by site pairs: index order (r1,c1,r2,c2,r3,c3)"""
    return C.reshape([d] * 6).transpose(0, 3, 1, 4, 2, 5).reshape(-1)
al = 0.37; d = 3
Om = np.zeros((d * d, 1));
for j in range(d): Om[j * d + j] = 1
rhoG = (np.eye(d * d) - al * Om @ Om.T) / (d * (d - al))     # rho_alpha^Gamma on one site pair
C = rng.normal(size=(27, 27)) + 1j * rng.normal(size=(27, 27))
vecC = site_perm_vec(C, d)
lhs = np.vdot(vecC, kron(rhoG, rhoG, rhoG) @ vecC).real
report("Prop. 2.1 matrix form, d=3", abs(lhs - q_alpha(C, [d]*3, al) / (d * (d - al)) ** 3) < 1e-9 * abs(lhs))

# ---------- 4. two-copy sum of squares ----------
dL, dR = 3, 4; D = dL * dR
def ptrL(M): return np.trace(M.reshape(dL, dR, dL, dR), axis1=0, axis2=2)
def ptrR(M): return np.trace(M.reshape(dL, dR, dL, dR), axis1=1, axis2=3)
def Lam(M): return (ptrL(M), ptrR(M))
def ipL(P, Q): return np.vdot(P[0], Q[0]) + np.vdot(P[1], Q[1])
def swapL(vv): return vv.reshape(dL, dR, dL, dR).transpose(2, 1, 0, 3).reshape(-1)
def swapR(vv): return vv.reshape(dL, dR, dL, dR).transpose(0, 3, 2, 1).reshape(-1)
def J(vv):
    w = vv - swapR(vv); w = w - swapL(w); return w / 4
def Qcut(C): return np.linalg.norm(C) ** 2 - 0.5 * (np.linalg.norm(ptrL(C)) ** 2 + np.linalg.norm(ptrR(C)) ** 2) + 0.25 * abs(np.trace(C)) ** 2
sig = [np.array([[0, 1], [1, 0]]), np.array([[0, -1j], [1j, 0]]), np.diag([1, -1])]
worst = 0.0; worstA1 = 0.0; worstA4 = 0.0
for trial in range(3):
    U = np.linalg.qr(rng.normal(size=(D, 2)) + 1j * rng.normal(size=(D, 2)))[0]
    V = np.linalg.qr(rng.normal(size=(D, 2)) + 1j * rng.normal(size=(D, 2)))[0]
    Sig = np.diag(np.sort(rng.uniform(0.3, 1.5, 2))[::-1]); S12 = np.sqrt(Sig)
    def dev(p):
        th = p[:3]; n = np.linalg.norm(th) + 1e-12
        W = np.cos(n) * np.eye(2) + 1j * np.sin(n) / n * sum(th[k] * sig[k] for k in range(3))
        H = (V @ S12 @ W).conj().T @ (U @ S12 @ W); return abs(H[0, 0] - H[1, 1]) ** 2
    res = min((minimize(dev, rng.normal(size=3)) for _ in range(6)), key=lambda r: r.fun)
    th = res.x; n = np.linalg.norm(th)
    W = np.cos(n) * np.eye(2) + 1j * np.sin(n) / n * sum(th[k] * sig[k] for k in range(3))
    X = U @ S12 @ W; Y = V @ S12 @ W; C = X @ Y.conj().T; H = Y.conj().T @ X; G = X.conj().T @ X
    n1, n2, om = G[0, 0].real, G[1, 1].real, G[0, 1]
    x1, x2 = X[:, 0], X[:, 1]; y1, y2 = Y[:, 0], Y[:, 1]
    eX = 4 * np.linalg.norm(J(np.kron(x1, x2))) ** 2; eY = 4 * np.linalg.norm(J(np.kron(y1, y2))) ** 2
    e1 = 4 * np.linalg.norm(J(np.kron(x1, y1))) ** 2; e2 = 4 * np.linalg.norm(J(np.kron(x2, y2))) ** 2
    Theta = np.outer(x2, x1.conj()) - np.outer(y2, y1.conj())
    rhs = (n1 - n2) ** 2 / 2 + abs(om) ** 2 + (eX + eY + e1 + e2 + ipL(Lam(Theta), Lam(Theta)).real) / 2
    worst = max(worst, abs(Qcut(C) - rhs), abs(H[0, 0] - H[1, 1]))
    # (A1) and (A4) for arbitrary vectors
    xa = rng.normal(size=D) + 1j * rng.normal(size=D); ya = rng.normal(size=D) + 1j * rng.normal(size=D)
    lhsA1 = ipL(Lam(np.outer(xa, ya.conj())), Lam(np.outer(xa, ya.conj()))).real
    rhsA1 = np.linalg.norm(xa) ** 2 * np.linalg.norm(ya) ** 2 + abs(np.vdot(ya, xa)) ** 2 - 4 * np.linalg.norm(J(np.kron(xa, ya))) ** 2
    worstA1 = max(worstA1, abs(lhsA1 - rhsA1))
    v1, v2, w1, w2 = (rng.normal(size=D) + 1j * rng.normal(size=D) for _ in range(4))
    lhsA4 = ipL(Lam(np.outer(v1, w1.conj())), Lam(np.outer(v2, w2.conj())))
    rhsA4 = ipL(Lam(np.outer(w2, w1.conj())), Lam(np.outer(v2, v1.conj())))
    worstA4 = max(worstA4, abs(lhsA4 - rhsA4))
report("(A1) on random vectors", worstA1 < 1e-9, f"max deviation {worstA1:.1e}")
report("(A2) on random vectors", worstA4 < 1e-9, f"max deviation {worstA4:.1e}")
report("(A3) two-site sum of squares, 3x4 balanced factors", worst < 1e-6, f"max deviation {worst:.1e}")

# ---------- 5. the zero families ----------
d = 3; dims = [d] * 3
sgm = np.array([[0, 1], [-1, 0]])
def embed():  # random local binary embedding C^2 -> C^3 at each site
    return [np.linalg.qr(rng.normal(size=(d, 2)) + 1j * rng.normal(size=(d, 2)))[0] for _ in range(3)]
def beta(r, iota):
    Xi = kron(*([sgm] * r)); return iota @ sgm @ iota.T @ np.linalg.inv(Xi) / np.sqrt(2)
vals = []
# family I
phi = rng.normal(size=9) + 1j * rng.normal(size=9); phi /= np.linalg.norm(phi)
eta = rng.normal(size=9) + 1j * rng.normal(size=9); eta /= np.linalg.norm(eta)
C1 = np.kron(PE, np.outer(phi, eta.conj())) / np.sqrt(2)
vals.append(("I", C1))
# family II
Vs = embed(); iota2 = np.linalg.qr(rng.normal(size=(4, 2)) + 1j * rng.normal(size=(4, 2)))[0]
V23 = kron(Vs[1], Vs[2]); b2 = V23 @ beta(2, iota2) @ V23.conj().T
aa = rng.normal(size=3) + 1j * rng.normal(size=3); aa /= np.linalg.norm(aa)
bb = rng.normal(size=3) + 1j * rng.normal(size=3); bb /= np.linalg.norm(bb)
vals.append(("II", np.kron(np.outer(aa, bb.conj()), b2)))
# family III
Vs = embed(); iota3 = np.linalg.qr(rng.normal(size=(8, 2)) + 1j * rng.normal(size=(8, 2)))[0]
V123 = kron(*Vs); vals.append(("III", V123 @ beta(3, iota3) @ V123.conj().T))
for name, C in vals:
    sv = np.linalg.svd(C, compute_uv=False)[:3]
    report(f"Prop. 4.2(a) family {name} is a zero with singular values (2^-1/2, 2^-1/2, 0)",
           abs(q_alpha(C, dims, 0.5)) < 1e-12 and np.allclose(sv, [2 ** -0.5, 2 ** -0.5, 0], atol=1e-10),
           f"q = {q_alpha(C, dims, 0.5):.1e}, svals = {np.round(sv, 6)}")

# ---------- 6. two elementary facts ----------
d1, d2, d3 = 3, 2, 3
C1 = rng.normal(size=(d1, d1)) + 1j * rng.normal(size=(d1, d1))
C2 = rng.normal(size=(d2 * d3, d2 * d3)) + 1j * rng.normal(size=(d2 * d3, d2 * d3))
al = 0.29
lhs = q_alpha(np.kron(C1, C2), [d1, d2, d3], al)
rhs = (np.linalg.norm(C1) ** 2 - al * abs(np.trace(C1)) ** 2) * q_alpha(C2, [d2, d3], al)
report("Lemma 2.4(a): q_alpha(C1 (x) C2) = q_1,alpha(C1) q_2,alpha(C2)", abs(lhs - rhs) < 1e-9 * abs(lhs))
Vs = [np.linalg.qr(rng.normal(size=(4, k)) + 1j * rng.normal(size=(4, k)))[0] for k in (d1, d2, d3)]
V = kron(*Vs); Cx = rng.normal(size=(18, 18)) + 1j * rng.normal(size=(18, 18))
report("Lemma 2.4(b): q_alpha(V C V^dagger) = q_alpha(C) for local isometries", abs(q_alpha(V @ Cx @ V.conj().T, [4, 4, 4], al) - q_alpha(Cx, [d1, d2, d3], al)) < 1e-9 * abs(q_alpha(Cx, [d1, d2, d3], al)))
# ---------- 7. Remark 3.2(a): rho_alpha = lam rho_{1/2} + (1-lam) I/d^2 ----------
for dd in (3, 4):
    F = swap(dd); al = 0.37; lam = al * (2 * dd - 1) / (dd - al)
    rho = lambda a_: (np.eye(dd * dd) - a_ * F) / (dd * (dd - a_))
    report(f"Remark 3.2(a) convex decomposition, d={dd}", np.allclose(rho(al), lam * rho(0.5) + (1 - lam) * np.eye(dd * dd) / dd**2) and 0 <= lam <= 1)
# ---------- 8. Remark 4.3: parity of the spin flip ----------
for r in (2, 3):
    Xi = kron(*([sgm] * r)).real
    iota = np.linalg.qr(rng.normal(size=(2**r, 2)) + 1j * rng.normal(size=(2**r, 2)))[0]; x, y = iota[:, 0], iota[:, 1]
    th = lambda psi: Xi @ psi.conj()
    b = (np.outer(x, th(y).conj()) - np.outer(y, th(x).conj())) / np.sqrt(2)
    if r == 3:
        report("Remark 4.3 odd r: beta^2 = (Tr beta/2) beta", np.linalg.norm(b @ b - np.trace(b) / 2 * b) < 1e-12)
    else:
        report("Remark 4.3 even r: Tr beta = 0", abs(np.trace(b)) < 1e-12)
print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
