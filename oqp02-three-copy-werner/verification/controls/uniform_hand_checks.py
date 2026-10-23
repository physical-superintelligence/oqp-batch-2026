#!/usr/bin/env python3
"""Numerical checks (not proofs) of the hand identities of Sec. VII and Appendix B of the paper:
   the determinant form det H_w = <r, K(w) r> and its permutations kappa (eq. (21)),
   the hand-cone products T_pm(a,a') (eq. (22)) and T_-(a,a) = 2 det H_a,
   the positivity of H_a for the one-/two-site weight vectors and for a_B (Theorem B.1),
   and every identity and inequality in the proof of Theorem B.1 (Appendix B).
Run:  python3 -I uniform_hand_checks.py     (needs numpy; about 20 s)"""
import os, sys, runpy
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'uniform'))
sys.argv = [sys.argv[0]]
for mod in ('kform', 'handcone'):
    print('--', mod, 'self-test')
    runpy.run_module(mod, run_name='__main__')
print('-- Appendix B (Theorem B.1) identities')
runpy.run_path(os.path.join(HERE, 'appendix_b_checks.py'), run_name='__main__')
print('ALL HAND CHECKS PASSED')
