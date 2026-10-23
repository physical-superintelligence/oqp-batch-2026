"""Bisection on alpha for the leading-order certificate SDP, for several sets of auxiliary inputs."""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..'))
import sys, json, time
import numpy as np
from sdp_solve import solve, DATA

modes = sys.argv[1:] or ['none', 'hand', 'lemma2', 'all']
log = open(sys.argv[1] + '_bisect.log', 'a') if False else open('bisect.log', 'a')


def names_for(mode):
    if mode == 'none':
        return []
    if mode == 'hand':
        return [n for n, _ in DATA['aux'] if 'lemma2' not in n]
    if mode == 'lemma2':
        return ['det lemma2']
    if mode == 'lemma2T':
        return [n for n, _ in DATA['aux'] if 'lemma2' in n]
    return None


for mode in modes:
    lo, hi = 0.40, 0.50
    hist = []
    while hi - lo > 2.5e-4:
        mid = round((lo + hi) / 2, 6)
        r = solve(mid, names_for(mode))
        feas = r['lam'] is not None and r['lam'] > 1e-7
        hist.append((mid, r["status"], float(r["lam"]) if r["lam"] is not None else None, bool(feas), round(r["time"])))
        msg = 'mode %s alpha %.6f status %s lambda %s feasible %s (%d s)' % (mode, mid, r['status'], r['lam'], feas, r['time'])
        print(msg, flush=True)
        log.write(msg + '\n'); log.flush()
        if feas:
            lo = mid
        else:
            hi = mid
    msg = 'RESULT mode %s: alpha in [%.6f, %.6f]' % (mode, lo, hi)
    print(msg, flush=True)
    log.write(msg + '\n'); log.flush()
    with open('bisect_%s.json' % mode, 'w') as f:
        json.dump({'mode': mode, 'lo': lo, 'hi': hi, 'hist': hist}, f, indent=1)
