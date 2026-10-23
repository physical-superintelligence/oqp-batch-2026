#!/usr/bin/env python3
"""
verify_circulation.py

Exact check of the two identities in the appendix "The circulation sum of squares" of

    D. Turturean and N. Bao, "The optimal CGLMP measurements on maximally entangled states".

Equations are named by their labels in the paper's LaTeX source.

Setting (from the paper). Fix i < j < k. The unitaries V_i, V_j, V_k satisfy V^4 = I and have the
spectral decompositions V_s = sum_{l in Z_4} i^l E_{s,l}: for each site s in {i, j, k}, the four
spectral projections E_{s,0}, ..., E_{s,3} are orthogonal projections summing to I (some may be
zero). The normalized trace is tr = Tr/r on r x r matrices, <X,Y> = tr(X^dag Y), and
||X||_2^2 = tr(X^dag X). Further,

    z_{st}  = tr(V_s^dag V_t)                                  (overlaps, sec:reduction)
    C_{ijk} = Im z_{ij} + Im z_{jk} - Im z_{ik}                (lem:circulation)
    p_{st}  = (1 - Re z_{st} + Im z_{st}) / 2                  (eq:forbidden)

and, with spectral indices read modulo four, the appendix writes

    u_l = E_{i,l} E_{j,l+2},   v_l = E_{j,l} E_{k,l+2},   z_l = E_{i,l} E_{k,l+2},
    a_l = E_{i,l} E_{j,l+1},   b_l = E_{j,l} E_{k,l+1},   c_l = E_{i,l} E_{k,l+1},

P = sum_l (||a_l||^2 + ||b_l||^2 + ||c_l||^2), O = sum_l (||u_l||^2 + ||v_l||^2 + ||z_l||^2), and
the six rows (X_{l,nu}, Y_{l,nu}, eps_nu) of Table tab:circulation:

    nu = 1:  X = z_l,           Y = a_l,           eps = +1
    nu = 2:  X = z_l^dag,       Y = b_{l+1}^dag,   eps = +1
    nu = 3:  X = v_{l+1},       Y = a_l^dag,       eps = +1
    nu = 4:  X = u_l,           Y = c_l,           eps = -1
    nu = 5:  X = u_l^dag,       Y = b_{l+2},       eps = +1
    nu = 6:  X = v_{l+3}^dag,   Y = c_l^dag,       eps = -1

Checked statements:

    eq:Cexpansion
        C_{ijk} = -2 sum_l ||z_l||^2 + 2 Re sum_l [ <u_l, z_l> + <v_l^dag, z_l^dag> ]
                  + 2 Re sum_{l,nu} eps_nu <X_{l,nu}, Y_{l,nu}>

    eq:circulationSOS, for sigma = +1 and for sigma = -1
        2P + 5O - sigma C_{ijk} = sum_{l,nu} ||Y_{l,nu} - sigma eps_nu X_{l,nu}||^2
                                  + 3 sum_l ||u_l - (sigma/3) z_l||^2
                                  + 3 sum_l ||v_l^dag - (sigma/3) z_l^dag||^2
                                  + (7/3 + 2 sigma) sum_l ||z_l||^2

    together with the signs of the weights 1, 3, 3 and 7/3 + 2 sigma on the right side of
    eq:circulationSOS (all positive for both signs, so the right side is >= 0), and the step
    P + O = p_{ij} + p_{jk} + p_{ik} that the appendix takes from eq:forbiddenspectral.

Method: exact cyclic-word arithmetic. Every quantity above is the normalized trace of a
noncommutative polynomial in the twelve projections E_{s,l}, with Gaussian-rational coefficients
(pairs of fractions.Fraction). The only relations used are relations that hold for every three
4-outcome projection-valued measures on C^r, for every r >= 1:

    (R1) E_{s,l}^dag = E_{s,l};
    (R2) E_{s,l} E_{s,m} = delta_{lm} E_{s,l} for two projections of the same site s;
    (R3) E_{s,3} = I - E_{s,0} - E_{s,1} - E_{s,2};
    (T1) tr(XY) = tr(YX);   (T2) tr(X^dag) = conj tr(X);   (T3) tr(I) = 1.

No relation between projections of different sites is used. Products are kept in normal form:
E_{s,3} is expanded by (R3) at each site, and adjacent letters of the same site are multiplied by
(R2), so every word alternates between sites and uses only the indices 0, 1, 2. In a trace, a
word whose first and last letters belong to the same site is rotated by (T1) and reduced by (R2);
the remaining cyclic word is represented by its lexicographically least rotation. Real and
imaginary parts use (T2): Re tr(X) = [tr(X) + tr(X^dag)]/2 and Im tr(X) = [tr(X) - tr(X^dag)]/(2i),
where X^dag reverses every word and conjugates every coefficient; so each real part is the half-sum
of a word and the word's adjoint. Each side of each identity is reduced to a combination of
cyclic words, and the two combinations are compared coefficient by coefficient, exactly. Every
reduction step holds for all such projections and every r, so equal coefficients prove each
identity for all V_i, V_j, V_k of the paper's setting: the check is symbolic, not a sample.

Controls. Corrupted versions of the identities must fail, to show that the comparison detects
errors: each sign eps_nu of Table tab:circulation is flipped in turn (eq:Cexpansion must then
fail), and the weight 7/3 is replaced by 2 (eq:circulationSOS must then fail for both signs).

Self-test of the word arithmetic. The cyclic-word normal forms are also evaluated on one explicit
example, three 4-outcome projection-valued measures on C^5 with exact Gaussian-rational entries
(projection ranks 2,1,1,1 at site i; 1,1,0,3 at site j, with a zero projection; 1,2,1,1 at site k),
and compared with the same quantities computed from the definitions by exact 5 x 5 matrix
arithmetic. The self-test checks the implementation; the proof of the identities is the symbolic
comparison above.

Usage (from the paper/ folder):
    python3 -I verification/verify_circulation.py

Exit status: 0 if every check holds, 1 if some check fails.
Requires Python 3.9 or later, standard library only. Run time: well under one second.
"""

import argparse
import hashlib
import os
import platform
import sys
import time
from fractions import Fraction

if sys.version_info < (3, 9):
    sys.exit("verify_circulation.py needs Python 3.9 or later")


# ---------------------------------------------------------------------------------------------
# Gaussian rationals: x + iy with x, y exact fractions.

class Gq:
    __slots__ = ("re", "im")

    def __init__(self, re=0, im=0):
        self.re = Fraction(re)
        self.im = Fraction(im)

    @staticmethod
    def of(x):
        return x if isinstance(x, Gq) else Gq(x)

    def __add__(self, other):
        other = Gq.of(other)
        return Gq(self.re + other.re, self.im + other.im)

    __radd__ = __add__

    def __neg__(self):
        return Gq(-self.re, -self.im)

    def __sub__(self, other):
        other = Gq.of(other)
        return Gq(self.re - other.re, self.im - other.im)

    def __mul__(self, other):
        other = Gq.of(other)
        return Gq(self.re * other.re - self.im * other.im, self.re * other.im + self.im * other.re)

    __rmul__ = __mul__

    def div_real(self, q):
        q = Fraction(q)
        return Gq(self.re / q, self.im / q)

    def conj(self):
        return Gq(self.re, -self.im)

    def is_zero(self):
        return self.re == 0 and self.im == 0

    def __eq__(self, other):
        other = Gq.of(other)
        return self.re == other.re and self.im == other.im

    def __hash__(self):
        return hash((self.re, self.im))

    def __repr__(self):
        return "%s%+si" % (self.re, self.im) if self.im else str(self.re)


I_POWERS = (Gq(1), Gq(0, 1), Gq(-1), Gq(0, -1))       # i^l for l = 0, 1, 2, 3


# ---------------------------------------------------------------------------------------------
# Noncommutative polynomials in the twelve projections E_{s,l}, in normal form.
# A letter is (s, l) with site s in "ijk" and index l in {0, 1, 2}; a word is a tuple of letters
# whose adjacent letters belong to different sites; the empty word is the identity I. A
# polynomial is a dict {word: Gaussian-rational coefficient} without zero coefficients.

SITES = ("i", "j", "k")
L4 = range(4)


def _clean(d):
    return {w: c for w, c in d.items() if not c.is_zero()}


def padd(*xs):
    out = {}
    for x in xs:
        for w, c in x.items():
            out[w] = out[w] + c if w in out else c
    return _clean(out)


def pscale(c, x):
    c = Gq.of(c)
    return _clean({w: c * v for w, v in x.items()})


def pmul2(x, y):
    out = {}
    for w1, c1 in x.items():
        for w2, c2 in y.items():
            if w1 and w2 and w1[-1][0] == w2[0][0]:
                # Same site at the junction: (R2). Both letters are minimal projections with
                # index 0, 1 or 2, so the product is the letter itself or zero.
                if w1[-1][1] != w2[0][1]:
                    continue
                w = w1 + w2[1:]
            else:
                w = w1 + w2
            c = c1 * c2
            out[w] = out[w] + c if w in out else c
    return _clean(out)


def pmul(*xs):
    out = {(): Gq(1)}
    for x in xs:
        out = pmul2(out, x)
    return out


def padj(x):
    """X^dag: reverse every word (R1) and conjugate every coefficient."""
    return _clean({tuple(reversed(w)): c.conj() for w, c in x.items()})


def E(s, l):
    """The spectral projection E_{s,l}, index l read modulo four; E_{s,3} is expanded by (R3)."""
    l %= 4
    if l < 3:
        return {((s, l),): Gq(1)}
    return {(): Gq(1), ((s, 0),): Gq(-1), ((s, 1),): Gq(-1), ((s, 2),): Gq(-1)}


# ---------------------------------------------------------------------------------------------
# Traces: combinations of cyclic words, dicts {canonical cyclic word: coefficient}.

def cyclic_word(w):
    """The canonical cyclic word of tr(w) for a normal-form word w, or None if tr(w) = 0."""
    while len(w) >= 2 and w[0][0] == w[-1][0]:
        # tr(x_1 ... x_n) = tr(x_n x_1 ... x_{n-1}) by (T1); x_n x_1 is a same-site product (R2).
        if w[0][1] != w[-1][1]:
            return None
        w = w[:-1]
    if len(w) <= 1:
        return w
    return min(w[m:] + w[:m] for m in range(len(w)))


def tr(x):
    out = {}
    for w, c in x.items():
        cw = cyclic_word(w)
        if cw is None:
            continue
        out[cw] = out[cw] + c if cw in out else c
    return _clean(out)


tadd, tscale = padd, pscale
TR_I = {(): Gq(1)}                                      # tr(I) = 1, (T3)


def tconj(T):
    """conj tr(w) = tr(w^dag) by (T2): reverse each cyclic word, conjugate each coefficient."""
    out = {}
    for w, c in T.items():
        cw = cyclic_word(tuple(reversed(w)))
        out[cw] = out[cw] + c.conj() if cw in out else c.conj()
    return _clean(out)


def Re(T):
    return tscale(Fraction(1, 2), tadd(T, tconj(T)))


def Im(T):
    return tscale(Gq(0, Fraction(-1, 2)), tadd(T, tscale(-1, tconj(T))))


def ip(X, Y):
    """<X, Y> = tr(X^dag Y)."""
    return tr(pmul(padj(X), Y))


def norm2(X):
    """||X||_2^2 = tr(X^dag X)."""
    return ip(X, X)


def compare(T1, T2):
    """Number of cyclic words whose coefficients differ (0 means the two traces are equal)."""
    return len(tadd(T1, tscale(-1, T2)))


# ---------------------------------------------------------------------------------------------
# The quantities of the appendix "The circulation sum of squares".

def V(s):
    return padd(*(pscale(I_POWERS[l], E(s, l)) for l in L4))


def overlap(s, t):
    """z_{st} = tr(V_s^dag V_t)."""
    return tr(pmul(padj(V(s)), V(t)))


def u(l): return pmul(E("i", l), E("j", l + 2))
def v(l): return pmul(E("j", l), E("k", l + 2))
def zp(l): return pmul(E("i", l), E("k", l + 2))        # the product z_l of the appendix
def a(l): return pmul(E("i", l), E("j", l + 1))
def b(l): return pmul(E("j", l), E("k", l + 1))
def c(l): return pmul(E("i", l), E("k", l + 1))


# Table tab:circulation: (X_{l,nu}, Y_{l,nu}, eps_nu), nu = 1, ..., 6.
TABLE = (
    (lambda l: zp(l),             lambda l: a(l),             +1),
    (lambda l: padj(zp(l)),       lambda l: padj(b(l + 1)),   +1),
    (lambda l: v(l + 1),          lambda l: padj(a(l)),       +1),
    (lambda l: u(l),              lambda l: c(l),             -1),
    (lambda l: padj(u(l)),        lambda l: b(l + 2),         +1),
    (lambda l: padj(v(l + 3)),    lambda l: padj(c(l)),       -1),
)
EPS = tuple(row[2] for row in TABLE)
TABLE_NAMES = ("(z_l, a_l)", "(z_l^dag, b_{l+1}^dag)", "(v_{l+1}, a_l^dag)", "(u_l, c_l)",
               "(u_l^dag, b_{l+2})", "(v_{l+3}^dag, c_l^dag)")
WEIGHT_Z = Fraction(7, 3)


def circulation():
    """C_{ijk} = Im z_{ij} + Im z_{jk} - Im z_{ik}."""
    return tadd(Im(overlap("i", "j")), Im(overlap("j", "k")), tscale(-1, Im(overlap("i", "k"))))


def forbidden(s, t):
    """p_{st} = (1 - Re z_{st} + Im z_{st}) / 2, eq:forbidden."""
    z = overlap(s, t)
    return tscale(Fraction(1, 2), tadd(TR_I, tscale(-1, Re(z)), Im(z)))


def forbidden_spectral(s, t):
    """sum_l sum_{u=1,2} tr(E_{s,l} E_{t,l+u}), the right side of eq:forbiddenspectral."""
    return tadd(*(tr(pmul(E(s, l), E(t, l + w))) for l in L4 for w in (1, 2)))


def P_sum():
    return tadd(*(tadd(norm2(a(l)), norm2(b(l)), norm2(c(l))) for l in L4))


def O_sum():
    return tadd(*(tadd(norm2(u(l)), norm2(v(l)), norm2(zp(l))) for l in L4))


def Z_sum():
    return tadd(*(norm2(zp(l)) for l in L4))


def cexpansion_rhs(eps):
    """The right side of eq:Cexpansion, with the signs eps_nu of Table tab:circulation."""
    first = tscale(-2, Z_sum())
    second = tscale(2, Re(tadd(*(tadd(ip(u(l), zp(l)), ip(padj(v(l)), padj(zp(l))))
                                 for l in L4))))
    third = tscale(2, Re(tadd(*(tscale(eps[n], ip(X(l), Y(l)))
                                for n, (X, Y, _) in enumerate(TABLE) for l in L4))))
    return tadd(first, second, third)


def sos_lhs(sigma, P, O, C):
    """2P + 5O - sigma C_{ijk}, the left side of eq:circulationSOS."""
    return tadd(tscale(2, P), tscale(5, O), tscale(-sigma, C))


def sos_rhs(sigma, eps, weight_z):
    """The right side of eq:circulationSOS and its weights (term group, weight, number of terms)."""
    third = Fraction(sigma, 3)
    squares = tadd(*(norm2(padd(Y(l), pscale(-sigma * eps[n], X(l))))
                     for n, (X, Y, _) in enumerate(TABLE) for l in L4))
    u_terms = tadd(*(norm2(padd(u(l), pscale(-third, zp(l)))) for l in L4))
    v_terms = tadd(*(norm2(padd(padj(v(l)), pscale(-third, padj(zp(l))))) for l in L4))
    wz = weight_z + 2 * sigma
    total = tadd(squares, tscale(3, u_terms), tscale(3, v_terms), tscale(wz, Z_sum()))
    weights = [("||Y_{l,nu} - sigma eps_nu X_{l,nu}||^2", Fraction(1), 4 * len(TABLE)),
               ("||u_l - (sigma/3) z_l||^2", Fraction(3), 4),
               ("||v_l^dag - (sigma/3) z_l^dag||^2", Fraction(3), 4),
               ("||z_l||^2", wz, 4)]
    return total, weights


# ---------------------------------------------------------------------------------------------
# Exact matrices with Gaussian-rational entries, for the self-test.

def mzero(r):
    return [[Gq(0) for _ in range(r)] for _ in range(r)]


def meye(r):
    m = mzero(r)
    for x in range(r):
        m[x][x] = Gq(1)
    return m


def madd(A, B):
    return [[A[x][y] + B[x][y] for y in range(len(A))] for x in range(len(A))]


def mscale(c, A):
    c = Gq.of(c)
    return [[c * A[x][y] for y in range(len(A))] for x in range(len(A))]


def mmul(A, B):
    r = len(A)
    return [[sum((A[x][m] * B[m][y] for m in range(r)), Gq(0)) for y in range(r)]
            for x in range(r)]


def madj(A):
    return [[A[y][x].conj() for y in range(len(A))] for x in range(len(A))]


def mtr(A):
    """Normalized trace Tr(A)/r."""
    r = len(A)
    return sum((A[x][x] for x in range(r)), Gq(0)).div_real(r)


def vinner(x, y):
    return sum((p.conj() * q for p, q in zip(x, y)), Gq(0))


def gaussian_integer_vectors(seed, count, r):
    """Deterministic vectors with entries x + iy, x, y in {-3, ..., 3} (a linear congruential
    generator, so the example is the same on every platform and Python version)."""
    state = seed
    out = []
    for _ in range(count):
        vec = []
        for _ in range(r):
            parts = []
            for _ in range(2):
                state = (1103515245 * state + 12345) % 2**31
                parts.append((state >> 16) % 7 - 3)
            vec.append(Gq(parts[0], parts[1]))
        out.append(vec)
    return out


def pvm_from_vectors(vectors, ranks):
    """Exact Gram-Schmidt (no normalization); outcome l projects onto the span of the next
    ranks[l] orthogonal vectors."""
    r = len(vectors[0])
    ortho = []
    for vec in vectors:
        w = list(vec)
        for q in ortho:
            coef = vinner(q, vec).div_real(vinner(q, q).re)
            w = [wx - coef * qx for wx, qx in zip(w, q)]
        if vinner(w, w).is_zero():
            raise ValueError("linearly dependent vectors in the self-test example")
        ortho.append(w)
    pvm, pos = [], 0
    for rank in ranks:
        Em = mzero(r)
        for w in ortho[pos:pos + rank]:
            n = vinner(w, w).re
            Em = madd(Em, [[(w[x] * w[y].conj()).div_real(n) for y in range(r)] for x in range(r)])
        pvm.append(Em)
        pos += rank
    return pvm


SELF_TEST_R = 5
SELF_TEST_PVMS = {"i": (101, (2, 1, 1, 1)), "j": (202, (1, 1, 0, 3)), "k": (303, (1, 2, 1, 1))}


def decimal(q, places=6):
    """Exact rounding of a fraction to a decimal string (for display only)."""
    n = round(Fraction(q) * 10**places)
    sign = "-" if n < 0 else ""
    n = abs(n)
    return "%s%d.%0*d" % (sign, n // 10**places, places, n % 10**places)


def self_test(checks, normal_forms):
    r = SELF_TEST_R
    mats = {s: pvm_from_vectors(gaussian_integer_vectors(seed, r, r), ranks)
            for s, (seed, ranks) in SELF_TEST_PVMS.items()}
    I_r = meye(r)

    pvm_ok = True
    for s in SITES:
        total = mzero(r)
        for l in L4:
            pvm_ok = pvm_ok and madj(mats[s][l]) == mats[s][l]
            total = madd(total, mats[s][l])
            for m in L4:
                prod = mmul(mats[s][l], mats[s][m])
                pvm_ok = pvm_ok and prod == (mats[s][l] if l == m else mzero(r))
        pvm_ok = pvm_ok and total == I_r
    ranks_ok = all(mtr(mats[s][l]) * r == SELF_TEST_PVMS[s][1][l] for s in SITES for l in L4)
    noncommuting = all(mmul(mats[s][0], mats[t][0]) != mmul(mats[t][0], mats[s][0])
                       for s, t in (("i", "j"), ("j", "k"), ("i", "k")))
    checks.add("self-test example: three 4-outcome projection-valued measures on C^%d (E^dag = E, "
               "E_l E_m = delta_lm E_l, sum_l E_l = I, ranks %s), pairwise noncommuting"
               % (r, "; ".join(",".join(str(x) for x in SELF_TEST_PVMS[s][1]) for s in SITES)),
               pvm_ok and ranks_ok and noncommuting)

    # Direct evaluation from the definitions, with exact matrix arithmetic.
    def M(s, l):
        return mats[s][l % 4]

    Vm = {s: [[sum((I_POWERS[l] * mats[s][l][x][y] for l in L4), Gq(0)) for y in range(r)]
              for x in range(r)] for s in SITES}

    def zm(s, t):
        return mtr(mmul(madj(Vm[s]), Vm[t]))

    def ipm(X, Y):
        return mtr(mmul(madj(X), Y))

    def n2m(X):
        return ipm(X, X)

    def um(l): return mmul(M("i", l), M("j", l + 2))
    def vm(l): return mmul(M("j", l), M("k", l + 2))
    def zpm(l): return mmul(M("i", l), M("k", l + 2))
    def am(l): return mmul(M("i", l), M("j", l + 1))
    def bm(l): return mmul(M("j", l), M("k", l + 1))
    def cm(l): return mmul(M("i", l), M("k", l + 1))

    table_m = ((zpm, am, +1), (lambda l: madj(zpm(l)), lambda l: madj(bm(l + 1)), +1),
               (lambda l: vm(l + 1), lambda l: madj(am(l)), +1), (um, cm, -1),
               (lambda l: madj(um(l)), lambda l: bm(l + 2), +1),
               (lambda l: madj(vm(l + 3)), lambda l: madj(cm(l)), -1))
    direct = {}
    direct["C_ijk"] = Gq(zm("i", "j").im + zm("j", "k").im - zm("i", "k").im)
    direct["P"] = sum((n2m(am(l)) + n2m(bm(l)) + n2m(cm(l)) for l in L4), Gq(0))
    direct["O"] = sum((n2m(um(l)) + n2m(vm(l)) + n2m(zpm(l)) for l in L4), Gq(0))
    Zm = sum((n2m(zpm(l)) for l in L4), Gq(0))
    second = sum((ipm(um(l), zpm(l)) + ipm(madj(vm(l)), madj(zpm(l))) for l in L4), Gq(0))
    third = sum((e * ipm(X(l), Y(l)) for X, Y, e in table_m for l in L4), Gq(0))
    direct["right side of eq:Cexpansion"] = Gq(-2 * Zm.re + 2 * second.re + 2 * third.re)
    for sigma in (1, -1):
        s3 = Fraction(sigma, 3)
        rhs = sum((n2m(madd(Y(l), mscale(-sigma * e, X(l)))) for X, Y, e in table_m for l in L4),
                  Gq(0))
        rhs = rhs + 3 * sum((n2m(madd(um(l), mscale(-s3, zpm(l)))) for l in L4), Gq(0))
        rhs = rhs + 3 * sum((n2m(madd(madj(vm(l)), mscale(-s3, madj(zpm(l))))) for l in L4), Gq(0))
        rhs = rhs + (WEIGHT_Z + 2 * sigma) * Zm
        direct["right side of eq:circulationSOS, sigma = %+d" % sigma] = rhs
    for s, t in (("i", "j"), ("j", "k"), ("i", "k")):
        z = zm(s, t)
        direct["p_%s%s" % (s, t)] = Gq((1 - z.re + z.im) / 2)

    # Evaluation of the cyclic-word normal forms on the same matrices.
    cache = {(): Gq(1)}

    def word_value(w):
        if w not in cache:
            prod = I_r
            for s, l in w:
                prod = mmul(prod, mats[s][l])
            cache[w] = mtr(prod)
        return cache[w]

    def evaluate(T):
        return sum((cf * word_value(w) for w, cf in T.items()), Gq(0))

    mismatched = [name for name in direct if evaluate(normal_forms[name]) != direct[name]]
    checks.add("self-test: the cyclic-word normal forms of C_ijk, P, O, p_ij, p_jk, p_ik and of the "
               "right sides of eq:Cexpansion and eq:circulationSOS (both signs) evaluate on the "
               "example to the values computed from the definitions with exact %d x %d matrices "
               "(%d quantities, %d distinct cyclic words evaluated)"
               % (r, r, len(direct), len(cache) - 1), not mismatched,
               "differing: %s" % ", ".join(mismatched))
    Cv, Pv, Ov = direct["C_ijk"].re, direct["P"].re, direct["O"].re
    checks.add("self-test example is not degenerate: C_ijk = %s, P = %s, O = %s (rounded to six "
               "decimals); C_ijk != 0 and |C_ijk| <= 2P + 5O"
               % (decimal(Cv), decimal(Pv), decimal(Ov)),
               Cv != 0 and abs(Cv) <= 2 * Pv + 5 * Ov and direct["C_ijk"].im == 0)


# ---------------------------------------------------------------------------------------------

class Checks:
    def __init__(self):
        self.items = []

    def add(self, name, passed, detail=None):
        self.items.append((name, bool(passed)))
        print("  %-7s %s" % ("ok" if passed else "FAILED", name))
        if detail and not passed:
            print("          " + detail)

    def failed(self):
        return [name for name, passed in self.items if not passed]


def script_sha256():
    try:
        with open(os.path.abspath(__file__), "rb") as fh:
            return hashlib.sha256(fh.read()).hexdigest()
    except OSError:
        return "unavailable"


def max_length(T):
    return max((len(w) for w in T), default=0)


def main(argv=None):
    argparse.ArgumentParser(
        description="Exact cyclic-word check of eq:Cexpansion and of eq:circulationSOS for "
                    "sigma = +1 and sigma = -1 (appendix 'The circulation sum of squares')."
    ).parse_args(argv)
    t_start = time.perf_counter()

    print("verify_circulation.py: exact check of eq:Cexpansion and of both signs of "
          "eq:circulationSOS,")
    print('appendix "The circulation sum of squares" of D. Turturean and N. Bao, "The optimal CGLMP')
    print('measurements on maximally entangled states".')
    print("Script SHA-256: %s" % script_sha256())
    print("Python %s; arithmetic: exact Gaussian rationals (pairs of fractions.Fraction); standard "
          "library only" % platform.python_version())
    print()
    print("Setting: the twelve spectral projections E_{s,l}, s in {i, j, k}, l in Z_4, with the")
    print("relations E^dag = E, E_{s,l} E_{s,m} = delta_lm E_{s,l}, sum_l E_{s,l} = I at each site and")
    print("no relation between sites; tr is linear and cyclic, tr(X^dag) = conj tr(X), tr(I) = 1.")
    print("Normal form: E_{s,3} = I - E_{s,0} - E_{s,1} - E_{s,2} expanded at each site, adjacent")
    print("same-site products reduced, every trace written in cyclic words (lexicographically least")
    print("rotation), every real part split into the half-sum of a word and the word's adjoint.")
    print()

    checks = Checks()

    C = circulation()
    P, O = P_sum(), O_sum()
    p = {(s, t): forbidden(s, t) for s, t in (("i", "j"), ("j", "k"), ("i", "k"))}
    print("Normal forms: C_ijk = Im z_ij + Im z_jk - Im z_ik has %d cyclic words (length %d); P has"
          " %d, O has %d" % (len(C), max_length(C), len(P), len(O)))
    print()

    print("Checks (symbolic, for every r and all V_i, V_j, V_k with V^4 = I)")
    rhs_c = cexpansion_rhs(EPS)
    n_diff = compare(C, rhs_c)
    # The separate terms of the right side of eq:Cexpansion, to report the length-3 cyclic words
    # that cancel in the sum.
    terms = [norm2(zp(l)) for l in L4]
    terms += [Re(ip(u(l), zp(l))) for l in L4] + [Re(ip(padj(v(l)), padj(zp(l)))) for l in L4]
    terms += [Re(ip(X(l), Y(l))) for X, Y, _ in TABLE for l in L4]
    long_words = {w for T in terms for w in T if len(w) == 3}
    passed = n_diff == 0 and max_length(rhs_c) == 2
    checks.add("eq:Cexpansion: C_ijk = -2 sum_l ||z_l||^2 + 2 Re sum_l [<u_l,z_l> + <v_l^dag,z_l^dag>]"
               " + 2 Re sum_{l,nu} eps_nu <X_{l,nu},Y_{l,nu}>, with the six rows of "
               "Table tab:circulation; the %d separate terms of the right side contain %d distinct "
               "cyclic words of length 3, %s"
               % (len(terms), len(long_words),
                  "all of which cancel, and both sides reduce to the same %d cyclic words of "
                  "length 2" % len(C) if passed else "and the two sides differ"),
               passed, "%d cyclic words have different coefficients" % n_diff)

    sos_rhs_forms = {}
    for sigma in (1, -1):
        lhs = sos_lhs(sigma, P, O, C)
        rhs, weights = sos_rhs(sigma, EPS, WEIGHT_Z)
        sos_rhs_forms[sigma] = rhs
        n_diff = compare(lhs, rhs)
        weight_text = ", ".join("%s (%d terms %s)" % (w, n, name) for name, w, n in weights)
        checks.add("eq:circulationSOS, sigma = %+d: 2P + 5O %s C_ijk = sum of squared norms; %s"
                   % (sigma, "-" if sigma == 1 else "+",
                      "both sides reduce to the same %d cyclic words (length <= %d)"
                      % (len(lhs), max_length(lhs)) if n_diff == 0 else "the two sides differ"),
                   n_diff == 0, "%d cyclic words have different coefficients" % n_diff)
        checks.add("eq:circulationSOS, sigma = %+d: weights %s; all positive, so 2P + 5O %s C_ijk >= 0"
                   % (sigma, weight_text, "-" if sigma == 1 else "+"),
                   all(w > 0 for _, w, _ in weights) and weights[3][1] == WEIGHT_Z + 2 * sigma)

    fs_ok = all(compare(p[(s, t)], forbidden_spectral(s, t)) == 0 for s, t in p)
    checks.add("eq:forbiddenspectral for the three edges: (1 - Re z_st + Im z_st)/2 = sum_l sum_{u=1,2} "
               "tr(E_{s,l} E_{t,l+u}) for st = ij, jk, ik", fs_ok)
    sum_ok = compare(tadd(P, O), tadd(*p.values())) == 0
    checks.add("P + O = p_ij + p_jk + p_ik, with p_st = (1 - Re z_st + Im z_st)/2 from eq:forbidden",
               sum_ok)
    print("  Consequence: |C_ijk| <= 2P + 5O <= 5(P + O) = 5(p_ij + p_jk + p_ik), which is "
          "eq:circulation.")
    print()

    print("Controls (each corrupted identity must fail)")
    for n in range(len(TABLE)):
        eps = tuple(-e if m == n else e for m, e in enumerate(EPS))
        n_diff = compare(C, cexpansion_rhs(eps))
        checks.add("eps_%d of Table tab:circulation, row %s, sign flipped: eq:Cexpansion fails "
                   "(%d cyclic words differ)" % (n + 1, TABLE_NAMES[n], n_diff), n_diff > 0)
    for sigma in (1, -1):
        rhs, _ = sos_rhs(sigma, EPS, Fraction(2))
        n_diff = compare(sos_lhs(sigma, P, O, C), rhs)
        checks.add("weight 7/3 replaced by 2: eq:circulationSOS, sigma = %+d, fails (%d cyclic words "
                   "differ)" % (sigma, n_diff), n_diff > 0)
    print()

    print("Self-test of the word arithmetic against exact matrices (not part of the proof)")
    normal_forms = {"C_ijk": C, "P": P, "O": O,
                    "right side of eq:Cexpansion": rhs_c,
                    "right side of eq:circulationSOS, sigma = +1": sos_rhs_forms[1],
                    "right side of eq:circulationSOS, sigma = -1": sos_rhs_forms[-1]}
    for (s, t), form in p.items():
        normal_forms["p_%s%s" % (s, t)] = form
    self_test(checks, normal_forms)
    print()

    print("Run time: %.2f s" % (time.perf_counter() - t_start))
    failed = checks.failed()
    if failed:
        print("FAILED: %d check%s did not hold (lines marked FAILED above)."
              % (len(failed), "" if len(failed) == 1 else "s"))
        return 1
    print("All checks hold: eq:Cexpansion is an identity, and eq:circulationSOS holds with positive "
          "weights for sigma = +1 and sigma = -1.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
