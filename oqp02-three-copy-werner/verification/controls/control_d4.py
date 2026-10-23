"""Independent end-to-end physical control of the GLiuax d=4 three-copy certificate.

Their verifier checks the rational identity  c^T x = sum_t Tr[Z_t M_t(x)] + eta^T E_0 x  and Z_t > 0.
It does NOT check that a physical matrix C actually produces coordinates x with E x = 0, M_t(x) >= 0
and c^T x = q3(C).  This script does that numerically (float64), using only: the literal definitions
(permutation operators on four replicas of V = C^4 x C^4 x C^4 x C^2), the stored source words
(diagrams_f.npz = orbit coefficients), the stored Gram maps (rational_maps/*.npz), E, c, Z_t, eta.

usage: python3 -I control_d4.py <datadir> <mode: random|zero|rank1|real> [seed]
"""
import sys, json, math, time
from fractions import Fraction
from itertools import permutations
import numpy as np
from scipy import sparse
import opt_einsum as oe

ROOT = sys.argv[1]
MODE = sys.argv[2] if len(sys.argv) > 2 else 'random'
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 0
RUN = ROOT + '/full_gram_crossed'
P = tuple(permutations(range(4)))
PI = {p: i for i, p in enumerate(P)}
INV = [PI[tuple(p.index(i) for i in range(4))] for p in P]
FAM = ('31', '22', '13')
t0 = time.time()


def cycles(p):
    seen = [False] * 4; c = 0
    for i in range(4):
        if not seen[i]:
            c += 1; j = i
            while not seen[j]:
                seen[j] = True; j = p[j]
    return c


def Tmat(d):
    # T[p,q] = Tr(V_p^T V_q) on (C^d)^{x4} = d^{cycles(p^{-1} q)}
    T = np.zeros((24, 24))
    for i, p in enumerate(P):
        pinv = P[INV[i]]
        for j, q in enumerate(P):
            comp = tuple(pinv[q[k]] for k in range(4))
            T[i, j] = d ** cycles(comp)
    return T


# ---------- the test matrix C (64 x 64, rank <= 2) and its lifting ----------
rng = np.random.default_rng(SEED)
if MODE == 'random':
    A = np.linalg.qr(rng.normal(size=(64, 2)) + 1j * rng.normal(size=(64, 2)))[0]
    B = rng.normal(size=(64, 2)) + 1j * rng.normal(size=(64, 2))
elif MODE == 'real':
    A = np.linalg.qr(rng.normal(size=(64, 2)))[0].astype(complex)
    B = rng.normal(size=(64, 2)).astype(complex)
elif MODE == 'rank1':
    A = np.linalg.qr(rng.normal(size=(64, 2)) + 1j * rng.normal(size=(64, 2)))[0]
    B = rng.normal(size=(64, 2)) + 1j * rng.normal(size=(64, 2)); B[:, 1] = 0
elif MODE == 'zero':
    # C0 = (|0><0| + |1><1|)/2 (x) |u><v| : exact zero of q3
    u = rng.normal(size=16) + 1j * rng.normal(size=16); u /= np.linalg.norm(u)
    v = rng.normal(size=16) + 1j * rng.normal(size=16); v /= np.linalg.norm(v)
    C = np.kron(np.diag([1, 1, 0, 0]) / 2, np.outer(u, v.conj()))
    U, S, Vh = np.linalg.svd(C); A = U[:, :2]; B = (2 * C.conj().T @ A)
else:
    raise SystemExit('mode?')
B *= np.sqrt(2 / np.vdot(B, B).real)
C = A @ B.conj().T / 2
assert np.linalg.norm(A.conj().T @ A - np.eye(2)) < 1e-12 and abs(np.vdot(C, C).real - 0.5) < 1e-12
# q3(C) directly
D = C.reshape((4,) * 6); q3 = 0.0
for mask in range(8):
    sites = [i for i in range(3) if mask >> i & 1]
    X = D; rem = 3
    for i in reversed(sites):
        X = np.trace(X, axis1=i, axis2=rem + i); rem -= 1
    q3 += (-0.5) ** len(sites) * np.vdot(X, X).real
print(f'mode {MODE} seed {SEED}: q3(C) = {q3:.12f}, |C C^+ - C^+ C| = {np.linalg.norm(C @ C.conj().T - C.conj().T @ C):.3e}', flush=True)

a = A.reshape(4, 4, 4, 2) / np.sqrt(2); b = B.reshape(4, 4, 4, 2) / np.sqrt(2)
replicas = {'31': [a, a, a, b], '22': [a, a, b, b], '13': [b, b, b, a]}

# ---------- moments m_f[w] = <Psi_f| D_w |Psi_f>, D_w = V_{w0} x V_{w1} x V_{w2} x V_{w3}^{(Q)} ----------
# V_p |x_1..x_4> = |x_{p^{-1}(1)} ... >  (site-wise on the four replicas)
letters = 'abcdefghijklmnop'
def moments(vs):
    m = np.zeros((24, 24, 24, 24), dtype=complex)
    I = [[letters[4 * r + s] for s in range(4)] for r in range(4)]   # input index of replica r, slot s
    for i0 in range(24):
        for i1 in range(24):
            for i2 in range(24):
                ps = [P[i0], P[i1], P[i2]]
                # output index of replica r at site s is input index of replica p_s^{-1}(r)
                pinv = [[p.index(r) for r in range(4)] for p in ps]
                ket = [''.join(I[r]) for r in range(4)]
                bra = [''.join([I[pinv[s][r]][s] for s in range(3)] + ['QRST'[r]]) for r in range(4)]
                out = ''.join(I[r][3] for r in range(4)) + 'QRST'          # q_in(1..4), q_out(1..4)
                spec = ','.join(ket + bra) + '->' + out
                ops = vs + [v.conj() for v in vs]
                expr = oe.contract_expression(spec, *[v.shape for v in ops], optimize='greedy')
                Tq = expr(*ops)   # shape (2,)*8
                Tq = Tq.reshape(16, 16)   # [q_in, q_out]
                for i3 in range(24):
                    pinv3 = [P[i3].index(r) for r in range(4)]
                    # q_out^{(r)} = q_in^{(pinv3[r])}
                    idx = np.arange(16)
                    bits = (idx[:, None] >> np.arange(3, -1, -1)[None, :]) & 1   # q_in^{(0..3)}
                    qout = sum(bits[:, pinv3[r]] << (3 - r) for r in range(4))
                    m[i0, i1, i2, i3] = Tq[idx, qout].sum()
    return m.ravel()

M = {}
for f in FAM:
    M[f] = moments(replicas[f])
    print(f'moments {f} done ({time.time()-t0:.0f}s); m[identity] = {M[f][0]:.6f}', flush=True)

# ---------- source coordinates x_f:  G_f x_f = s * Re <B_k, Y_f> ----------
src = json.load(open(ROOT + '/source.json'))
s_scale = src['normalization']
T4 = Tmat(4); T2 = Tmat(2)
x = {}; Gcond = {}
for f in FAM:
    Bm = sparse.load_npz(ROOT + f'/diagrams_{f}.npz').tocsc().astype(float)
    den = src['basis_verification'][f]['diagram_denominator']
    n = Bm.shape[1]
    # orbit coefficients are transpose-symmetric: check on a few columns
    for k in (0, n // 2, n - 1):
        col = Bm[:, k].toarray().ravel().reshape(24, 24, 24, 24)
        colinv = np.zeros_like(col)
        for w in zip(*np.nonzero(col)):
            colinv[INV[w[0]], INV[w[1]], INV[w[2]], INV[w[3]]] = col[w]
        assert np.array_equal(col, colinv)
    rhs = (Bm.T @ M[f]) / den                       # <B_k, Y> up to transpose (orbit symmetric)
    G = np.zeros((n, n))
    for c0 in range(0, n, 150):
        chunk = Bm[:, c0:c0 + 150].toarray().reshape(24, 24, 24, 24, -1)
        TB = np.einsum('ia,abcde->ibcde', T4, chunk)
        TB = np.einsum('jb,ibcde->ijcde', T4, TB)
        TB = np.einsum('kc,ijcde->ijkde', T4, TB)
        TB = np.einsum('ld,ijkde->ijkle', T2, TB)
        G[:, c0:c0 + 150] = (Bm.T @ TB.reshape(-1, TB.shape[-1])) / den ** 2
    assert np.allclose(G, G.T, rtol=1e-9, atol=1e-6)
    ev = np.linalg.eigvalsh(G); Gcond[f] = ev.max() / ev.min()
    xf = np.linalg.solve(G, s_scale * rhs.real)
    resid = np.linalg.norm(G @ xf - s_scale * rhs.real) / np.linalg.norm(s_scale * rhs.real)
    imag = np.abs(rhs.imag).max() / (np.abs(rhs.real).max() + 1e-300)
    x[f] = xf
    print(f'family {f}: dim {n}, Gram cond {Gcond[f]:.2e}, solve resid {resid:.2e}, max Im/Re of <B,Y> {imag:.2e} ({time.time()-t0:.0f}s)', flush=True)
xall = np.concatenate([x[f] for f in FAM])
starts = {'31': 0, '22': 667, '13': 2074}

# objective
c = np.array([float(Fraction(v)) for v in src['objective']])
obj = c @ xall
print(f'OBJECTIVE  c^T x = {obj:.12f}   q3(C) = {q3:.12f}   diff = {obj-q3:.3e}', flush=True)
# trace normalisation: 'traces' should give Tr(Y_f) * s ?  report
tr = np.array([float(Fraction(v)) for v in src['traces']])
print(f'traces: tr^T x = {tr @ xall:.6f} (expect 3 * s = {3*s_scale} if each moment has unit trace)', flush=True)

# equalities
E = sparse.load_npz(ROOT + '/equality_integer.npz').astype(float)
Ex = E @ xall
print(f'EQUALITIES |E x|_inf = {np.abs(Ex).max():.3e}  relative to |E|_inf |x|_inf = {abs(E).max()*np.abs(xall).max():.3e}  -> rel {np.abs(Ex).max()/(abs(E).max()*np.abs(xall).max()):.3e}', flush=True)

# blocks
recs = json.load(open(RUN + '/frames.json'))['records']
lam_min = []; total = 0.0; worst = (0, None); nneg = 0
Zsum = 0.0
for rec in recs:
    idx = rec['index']; k = rec['order']
    data = np.load(RUN + '/rational_maps/%04d.npz' % idx)
    fams = list(data['families'])
    xf = np.concatenate([x[f] for f in fams])
    v = (data['integer'].astype(float).T @ xf) / float(data['denominator'])
    Mt = np.zeros((k, k)); col = 0
    for j in range(k):
        for i in range(j, k):
            Mt[i, j] = v[col] if i == j else v[col] / 2
            Mt[j, i] = Mt[i, j]; col += 1
    ev = np.linalg.eigvalsh(Mt)
    scale = max(np.abs(Mt).max(), 1e-300)
    lam_min.append((ev.min(), scale, idx, k, rec['type']))
    if ev.min() < -1e-7 * max(scale, 1.0): nneg += 1
    cert = json.load(open(RUN + '/rational_certificate/%04d.json' % idx))
    Z = np.array([[float(Fraction(e)) for e in row] for row in cert['Z']])
    Zsum += np.trace(Z @ Mt)
eq = json.load(open(RUN + '/rational_certificate/equality.json'))
eta = np.array([float(Fraction(v)) for v in eq['coefficients']])
E0x = (E[eq['rows'], :] @ xall)
ident = Zsum + eta @ E0x
rel = [(l / max(sc, 1.0), idx, k, ty) for l, sc, idx, k, ty in lam_min]
rel.sort()
print(f'BLOCKS: {len(lam_min)} compressions; most negative relative eigenvalue {rel[0][0]:.3e} (block {rel[0][1]}, order {rel[0][2]}, {rel[0][3]}); blocks with lambda_min < -1e-7*scale: {nneg}', flush=True)
absmax = max(sc for _, sc, *_ in lam_min)
print(f'        max |M_t| = {absmax:.3e}; number of blocks with |M_t| < 1e-9*max: {sum(sc < 1e-9*absmax for _, sc, *_ in lam_min)}', flush=True)
print(f'IDENTITY sum_t Tr[Z_t M_t(x)] = {Zsum:.12f}, eta^T E_0 x = {eta @ E0x:.3e}, total = {ident:.12f}, c^T x = {obj:.12f}, diff {ident-obj:.3e}', flush=True)
print(f'done {time.time()-t0:.0f}s', flush=True)
