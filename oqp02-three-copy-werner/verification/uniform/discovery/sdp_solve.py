"""Solve the leading-order certificate SDP at a given alpha: maximize the uniform block margin lambda."""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..'))
import pickle, sys, time
from fractions import Fraction
import numpy as np
import scipy.sparse as sp
import cvxpy as cp
from sdp_setup import MONOS, MIDX, IDEAL, TAUS5, tensor_vec
from kform import K_of_weights, weights_alpha

with open('sdp_data.pkl', 'rb') as f:
    DATA = pickle.load(f)


def solve(alpha, aux_names=None, solver='CLARABEL', verbose=False, lam_cap=None, extra=None,
          exact_identity=False, tol=None, max_iter=None):
    d = DATA
    nf, n0 = len(d['reps_full']), len(d['reps_0'])
    z = {tau: cp.Variable(n0 if tau == (0,) else nf) for tau in TAUS5 if not (exact_identity and tau == ())}
    aux = [(n, T) for (n, T) in d['aux'] if aux_names is None or n in aux_names]
    mu = cp.Variable(len(aux), nonneg=True) if aux else None
    lam = cp.Variable()
    rep_all = [MIDX[m] for m in d['reps_full']]
    rep_rows = [MIDX[m] for k, m in enumerate(d['reps_full']) if not IDEAL[MIDX[m]]]
    a = alpha if isinstance(alpha, Fraction) else Fraction(alpha).limit_denominator(10**9)
    Kv = tensor_vec(K_of_weights(weights_alpha(a)))
    cons = []
    if exact_identity:
        # Y_() on full-orbit representatives is an affine function of the other variables
        ideal_mask = np.array([1.0 if IDEAL[i] else 0.0 for i in rep_all])
        e = cp.Variable(nf)  # free on ideal orbits only
        Ss_all = d['S_single'][rep_all]
        y0 = Kv[rep_all] - Ss_all @ z[(0,)] - z[(0, 1)] - z[(0, 2)] - z[(0, 3)]
        if aux:
            C_all = np.stack([tensor_vec(T)[rep_all] for _, T in aux], axis=1)
            y0 = y0 - C_all @ mu
        y0 = cp.multiply(1 - ideal_mask, y0) + cp.multiply(ideal_mask, e)
        z[()] = y0
    else:
        Sf = d['S_full'][rep_rows]
        Ss = d['S_single'][rep_rows]
        expr = Sf @ z[()] + Ss @ z[(0,)] + Sf @ z[(0, 1)] + Sf @ z[(0, 2)] + Sf @ z[(0, 3)]
        if aux:
            C = np.stack([tensor_vec(T)[rep_rows] for _, T in aux], axis=1)
            expr = expr + C @ mu
        cons.append(expr == Kv[rep_rows])
    if lam_cap is not None:
        cons.append(lam <= lam_cap)
    for tau in TAUS5:
        sb, maps = d['blocks'][tau]
        for (trip, n, M) in maps:
            B = cp.reshape(sp.csr_matrix(M) @ z[tau], (n, n), order='C')
            cons.append((B + B.T) / 2 - lam * np.eye(n) >> 0)
    prob = cp.Problem(cp.Maximize(lam), cons)
    t0 = time.time()
    kw = {}
    if tol is not None:
        kw.update(dict(tol_gap_abs=tol, tol_gap_rel=tol, tol_feas=tol, tol_infeas_abs=tol, tol_infeas_rel=tol, tol_ktratio=tol * 100))
    if max_iter is not None:
        kw['max_iter'] = max_iter
    prob.solve(solver=solver, verbose=verbose, **kw)
    out = {'status': prob.status, 'lam': lam.value, 'time': time.time() - t0,
           'z': {tau: (z[tau].value if not exact_identity or tau != () else None) for tau in TAUS5},
           'mu': (mu.value if aux else None), 'aux': [n for n, _ in aux]}
    if exact_identity:
        out['e'] = e.value
    return out


if __name__ == '__main__':
    alpha = float(sys.argv[1]) if len(sys.argv) > 1 else 0.45
    mode = sys.argv[2] if len(sys.argv) > 2 else 'none'
    if mode == 'none':
        names = []
    elif mode == 'hand':
        names = [n for n, _ in DATA['aux'] if 'lemma2' not in n]
    elif mode == 'lemma2':
        names = [n for n, _ in DATA['aux'] if n == 'det lemma2']
    else:
        names = None
    r = solve(alpha, names, verbose=('-v' in sys.argv))
    print('alpha', alpha, 'mode', mode, 'status', r['status'], 'lambda', r['lam'], 'time %.0f s' % r['time'])
    if r['mu'] is not None:
        for n, m in zip(r['aux'], r['mu']):
            if m > 1e-6:
                print('   mu', n, m)
