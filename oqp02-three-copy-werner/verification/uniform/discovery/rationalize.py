"""Round a numerical SDP solution (exact-identity parametrisation) to an exact rational certificate.
Usage: python3 rationalize.py <alpha0 as p/q> <mode> [bits] [tol] [max_iter]"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..'))
import sys, json
from fractions import Fraction
import numpy as np
from sdp_solve import solve, DATA
from sdp_setup import MONOS, MIDX, IDEAL, TAUS5, act, V4, IDENT, tensor_vec
from kform import K_of_weights, weights_alpha

F = Fraction


def str_of_mono(m):
    return '|'.join(''.join(str(c) for c in p) for p in m)


def names_for(mode):
    if mode == 'none':
        return []
    if mode == 'hand':
        return [n for n, _ in DATA['aux'] if 'lemma2' not in n]
    if mode == 'lemma2':
        return ['det lemma2']
    if mode == 'lemma2T':
        return [n for n, _ in DATA['aux'] if 'lemma2' in n]
    if mode.startswith('list:'):
        return mode[5:].split(';')
    return None


def main():
    alpha0 = F(sys.argv[1])
    mode = sys.argv[2]
    bits = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    tol = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-9
    max_iter = int(sys.argv[5]) if len(sys.argv) > 5 else 400
    r = solve(alpha0, names_for(mode), exact_identity=True, tol=tol, max_iter=max_iter)
    print('numerical solve:', r['status'], 'lambda =', r['lam'], 'time %.0f s' % r['time'])
    assert r['lam'] is not None and r['lam'] > 0
    den = 2 ** bits
    rnd = lambda x: F(int(round(x * den)), den)
    mu = {}
    if r['mu'] is not None:
        for n, v in zip(r['aux'], r['mu']):
            mu[n] = rnd(max(v, 0.0))
    auxT = dict(DATA['aux'])
    d = DATA
    reps_full, reps_0 = d['reps_full'], d['reps_0']
    orb_full, orb_0 = d['orb_full'], d['orb_0']
    y = {}
    for tau in TAUS5[1:]:
        reps = reps_0 if tau == (0,) else reps_full
        y[tau] = {str_of_mono(m): rnd(r['z'][tau][k]) for k, m in enumerate(reps)}
    K = K_of_weights(weights_alpha(alpha0))
    y0 = {}
    for k, m in enumerate(reps_full):
        if IDEAL[MIDX[m]]:
            y0[str_of_mono(m)] = rnd(r['e'][k])
            continue
        val = K.get(m, F(0))
        for n, v in mu.items():
            val -= v * auxT[n].get(m, F(0))
        for tau in ((0, 1), (0, 2), (0, 3)):
            val -= y[tau][str_of_mono(reps_full[orb_full[MIDX[m]]])]
        for g in V4:
            m2 = act(m, (0, 1, 2), g, False)
            val -= y[(0,)][str_of_mono(reps_0[orb_0[MIDX[m2]]])]
        y0[str_of_mono(m)] = val
    y[()] = y0
    out = {'alpha0': str(alpha0), 'epsilon': str(F(r['lam'] / 2).limit_denominator(10 ** 12)),
           'mu': {k: str(v) for k, v in mu.items() if v != 0},
           'y': {str(tau): {k: str(v) for k, v in y[tau].items() if v != 0} for tau in TAUS5},
           'numerical_margin': float(r['lam']), 'mode': mode, 'rounding_bits': bits}
    fn = 'certificate_uniform.json'
    with open(fn, 'w') as f:
        json.dump(out, f, indent=0)
    print('written', fn, '; epsilon =', out['epsilon'], '; nonzero mu:', {k: float(v) for k, v in mu.items() if v != 0})


if __name__ == '__main__':
    main()
