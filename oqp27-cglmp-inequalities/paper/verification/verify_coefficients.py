#!/usr/bin/env python3
"""
verify_coefficients.py

Executes the exact rational interval computation of the appendix "Bounds on the error
coefficients", subsection "The interval computation: proof of (ii)", of

    D. Turturean and N. Bao, "The optimal CGLMP measurements on maximally entangled states".

It certifies part (ii) of the lemma "Bounds on the error coefficients": for every 2 <= d <= 65
and every 1 <= k < d (2080 pairs),

    1/(3(d+1)) + e_{d,k} - (5/(2d)) l_{d,k}  >=  1/(6(d+1)),                (eq:finitecondition)

and the bound printed for the normalized margin,

    (d+1) [ 1/(3(d+1)) + min_k e_{d,k} - (5/(2d)) max_k l_{d,k} ]  >=  1935/10^4  >  1/6.

It also computes an upper bound of the normalized margin for each d, which locates the smallest
normalized margin: the paper's worst dimension, d = 7.

Equations are named by their labels in the paper's LaTeX source:
    eq:es               e_{d,k} = sigma(k/d) - (B_d sigma)(k) - (1/d)(B_d b)(k)
    eq:load             l_{d,k} = sum_{j=1}^{k-1} |t_j + t_{k-j} - t_k|
                                + sum_{j=k+1}^{d-1} |t_k + t_{j-k} - t_j|
    eq:finitecondition  the inequality displayed above
    eq:rn               r_n = 2 (2^(2n-1) - 1) |B_2n| / (2n)! * (pi/2)^(2n-1)
    eq:finiteeseries    e_{d,k} = sum_{n>=1} r_n [ y^j - (1 + (j+1)(j+2)/(2d)) m_j
                                                     + (j(j+1)/(2d)) m_{j-1} ],
                        j = 2n-1, y = 1 - k/d
    eq:finitetail       T_d = 3 sum_{n>=33} 4^(-n) (2 + 4n^2/(d+1))
Here t_k = e_{d,d-k} - e_{d,k} are the skew coefficients, and m_j are the moments
m_j = (d/(d+1)) (d-k+1)_j / (d+2)_j of the same appendix.

Arithmetic: every endpoint is an exact rational number, of type fractions.Fraction (Python
standard library) or, when the gmpy2 package is installed, gmpy2.mpq, which is faster and
gives identical results. As printed in the paper, the enclosure of pi from Machin's identity is
rounded outward to 80 decimal places and the enclosures of r_n to 60; there is no other
rounding. No floating-point arithmetic enters the computation or any comparison;
floating-point numbers appear only in the reported run times.

Usage:
    python3 verify_coefficients.py [--dmin D] [--dmax D] [--jobs N] [--json FILE]
                                  [--control C1|C2|C3]

    --dmin, --dmax   range of d (default 2 and 65)
    --jobs N         number of worker processes, one value of d at a time (default 1)
    --json FILE      also write the results to FILE: exact rationals as strings "p/q",
                     decimals with 30 significant digits rounded outward, run times
    --control C      a deliberately corrupted run that must fail (exit status 1):
                     C1  the bound 1935/10^4 for the normalized margin is replaced by the
                         computed minimum plus 10^-6;
                     C2  the load factor 5/(2d) is replaced by 5/d;
                     C3  the sign of B_10 is flipped when it is generated, so that the
                         recursion carries the error into B_11, ..., B_64.

Exit status: 0 if every assertion holds, 1 if some assertion fails, 2 for invalid arguments.
Requires Python 3.9 or later; gmpy2 is optional.
"""

import argparse
import hashlib
import json
import os
import platform
import sys
import time
from math import comb, factorial

if sys.version_info < (3, 9):
    sys.exit("verify_coefficients.py needs Python 3.9 or later")

if hasattr(sys, "set_int_max_str_digits"):
    # Exact results are printed as strings "p/q". Python 3.11 and later limit int <-> str
    # conversions to 4,300 digits by default; lift the limit.
    sys.set_int_max_str_digits(0)

try:
    import gmpy2

    Rational = gmpy2.mpq
    ARITHMETIC = "gmpy2 %s (mpq; %s)" % (gmpy2.version(), gmpy2.mp_version())
except ImportError:
    from fractions import Fraction as Rational

    gmpy2 = None
    ARITHMETIC = "fractions.Fraction (standard library; gmpy2 is not installed)"

# ---------------------------------------------------------------------------------------------
# Parameters, as printed in the subsection "The interval computation: proof of (ii)" and in its
# table "Data for the finite interval computation" (tab:intervals).

D_LOW, D_HIGH = 2, 65            # outcome counts 2 <= d <= 65
PAIRS_FULL_RANGE = 2080          # "checks all 2,080 pairs"; separations 1 <= k < d
N_TERMS = 32                     # "Truncating (finiteeseries) after 32 terms"; 1 <= n <= 32
TAIL_RHO = Rational(1, 4)        # the closed forms are evaluated "at q = 1/4"
TAIL_J = 33                      # tail start J = 33 in eq:finitetail
ARCTAN_TERMS = (128, 129)        # arctangent partial sums with 128 and 129 terms
PI_PLACES = 80                   # "The Machin enclosure is rounded outward to 80 decimal places
R_PLACES = 60                    # and the r_n enclosures to 60"
BERNOULLI_LAST = 64              # Bernoulli numbers "through m = 64"
MOMENT_LAST = 63                 # moment indices 0 <= j <= 63
MARGIN_BOUND = Rational(1935, 10**4)   # normalized margin ">= 1935/10^4 > 1/6"
ONE_SIXTH = Rational(1, 6)

# Values printed in the paper: "The worst dimension is d = 7, and the certified minimum
# normalized margin exceeds 0.19354436777798498." Both are compared when the run covers
# 2 <= d <= 65.
PRINTED_D = 7
PRINTED_MARGIN_TEXT = "0.19354436777798498"
PRINTED_MARGIN = Rational(19354436777798498, 10**17)

# Published values used only as consistency checks (they are not inputs of the computation):
# pi to 60 decimals (OEIS A000796); B_0, B_2, ..., B_14 and B_64 (OEIS A000367 and A002445, the
# numerators and denominators of B_2n); B_1 = -1/2, the value that this recursion gives.
PI_60_DECIMALS = "3.141592653589793238462643383279502884197169399375105820974944"
KNOWN_BERNOULLI = {
    0: (1, 1), 1: (-1, 2), 2: (1, 6), 4: (-1, 30), 6: (1, 42), 8: (-1, 30), 10: (5, 66),
    12: (-691, 2730), 14: (7, 6),
    64: (-106783830147866529886385444979142647942017, 510),
}

CONTROLS = {
    "C1": "the bound 1935/10^4 for the normalized margin is replaced by the computed minimum "
          "plus 10^-6",
    "C2": "the load factor 5/(2d) is replaced by 5/d",
    "C3": "the sign of B_10 is flipped when it is generated (the recursion carries the error "
          "into B_11, ..., B_64)",
}


# ---------------------------------------------------------------------------------------------
# Interval arithmetic with exact rational endpoints ("interval arithmetic [Moore]").

class Interval:
    """The closed interval [lo, hi], lo <= hi, with exact rational endpoints."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        self.lo = lo
        self.hi = hi

    def __add__(self, other):
        # [a, b] + [c, d] = [a + c, b + d]
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other):
        # [a, b] - [c, d] = [a - d, b - c]
        return Interval(self.lo - other.hi, self.hi - other.lo)

    def times(self, c):
        # c [a, b] for an exact rational c, respecting the sign of c:
        # [c a, c b] if c >= 0 and [c b, c a] if c < 0.
        if c >= 0:
            return Interval(c * self.lo, c * self.hi)
        return Interval(c * self.hi, c * self.lo)

    def abs_upper(self):
        # "bounding each absolute value |[l,u]| by max(|l|,|u|)"
        return max(abs(self.lo), abs(self.hi))

    def abs_lower(self):
        # Lower bound of |x| for x in [l,u]: 0 if l <= 0 <= u, and min(|l|,|u|) otherwise.
        if self.lo <= 0 <= self.hi:
            return Rational(0)
        return min(abs(self.lo), abs(self.hi))

    def rounded(self, places):
        # Outward rounding to `places` decimal places: the lower endpoint is rounded down and the
        # upper endpoint up, so the rounded interval contains [lo, hi].
        scale = 10**places
        p, q = _ints(self.lo)
        lo = Rational(p * scale // q, scale)
        p, q = _ints(self.hi)
        hi = Rational(-((-p * scale) // q), scale)
        return Interval(lo, hi)


# ---------------------------------------------------------------------------------------------
# Decimal output with outward (directed) rounding, by integer arithmetic only.

def _ints(x):
    return int(x.numerator), int(x.denominator)


def fixed(x, places, direction):
    """x with `places` decimals, rounded toward -infinity ("down") or +infinity ("up")."""
    p, q = _ints(x)
    scaled = p * 10**places
    v = scaled // q if direction == "down" else -((-scaled) // q)
    sign = "-" if v < 0 else ""
    s = str(abs(v)).rjust(places + 1, "0")
    return sign + s[:-places] + "." + s[-places:]


def _at_least_pow10(a, q, e):
    """a/q >= 10^e, for integers a >= 0, q > 0 and any integer e."""
    return a * 10**max(0, -e) >= q * 10**max(0, e)


def scientific(x, direction, digits=30):
    """x with `digits` significant digits, rounded toward -infinity ("down") or +infinity ("up")."""
    p, q = _ints(x)
    if p == 0:
        return "0"
    negative = p < 0
    a = -p if negative else p
    e = ((a.bit_length() - q.bit_length()) * 30103) // 100000   # first guess of log10(a/q)
    while not _at_least_pow10(a, q, e):
        e -= 1
    while _at_least_pow10(a, q, e + 1):
        e += 1
    shift = digits - 1 - e
    num = a * 10**max(0, shift)
    den = q * 10**max(0, -shift)
    round_magnitude_up = (direction == "up") != negative
    m = -((-num) // den) if round_magnitude_up else num // den
    if m == 10**digits:            # rounding up reached the next power of ten
        m //= 10
        e += 1
    s = str(m)
    return "%s%s.%se%+d" % ("-" if negative else "", s[0], s[1:], e)


def exact(x):
    """The exact rational x as the string "p/q" (or "p" when q = 1), the same for both
    arithmetic types."""
    return str(x)


def sha256_text(s):
    return hashlib.sha256(s.encode("ascii")).hexdigest()


def common_decimals(lo, hi, max_places=40):
    """The decimals on which every number in [lo, hi] agrees (0 < lo <= hi): the longest
    m <= max_places with floor(lo 10^m) = floor(hi 10^m), as the string "0.dddd"."""
    a = fixed(lo, max_places, "down")
    b = fixed(hi, max_places, "down")
    n = 0
    while n < len(a) and a[n] == b[n]:
        n += 1
    head = a[:n]
    return head if "." in head else ""


# ---------------------------------------------------------------------------------------------
# The computation, in the order of the subsection "The interval computation: proof of (ii)":
# "For 2 <= d <= 65, the inequality (finitecondition) is a finite set of rational comparisons,
# verified in exact interval arithmetic as follows." (main() counts the pairs; compute_d() makes
# the comparisons.)
# First the tail bound T_d of eq:finitetail.

def tail_sums(rho, J):
    """The closed forms printed in the subsection (there with q in place of rho):
        sum_{n>=J} rho^n     = rho^J / (1 - rho),
        sum_{n>=J} n^2 rho^n = rho^J [ J^2/(1-rho) + 2 J rho/(1-rho)^2 + rho(1+rho)/(1-rho)^3 ]."""
    s0 = rho**J / (1 - rho)
    s2 = rho**J * (Rational(J * J) / (1 - rho) + 2 * J * rho / (1 - rho)**2
                   + rho * (1 + rho) / (1 - rho)**3)
    return s0, s2


def tail_bound(d):
    """eq:finitetail: T_d = 3 sum_{n>=33} 4^(-n) (2 + 4n^2/(d+1)) = 3 [2 S0 + (4/(d+1)) S2],
    with S0, S2 the closed forms at rho = 1/4 and J = 33 (exact)."""
    s0, s2 = tail_sums(TAIL_RHO, TAIL_J)
    return 3 * (2 * s0 + Rational(4, d + 1) * s2)


# Then the enclosure of pi (Machin's identity), the Bernoulli numbers and r_n of eq:rn.

def arctan_partial_sum(a, N):
    """A(a,N) = sum_{i=0}^{N-1} (-1)^i / [(2i+1) a^(2i+1)], the sum of the first N terms of the
    series for arctan(1/a)."""
    s = Rational(0)
    for i in range(N):
        term = Rational(1, (2 * i + 1) * a**(2 * i + 1))
        s = s + term if i % 2 == 0 else s - term
    return s


def pi_enclosure():
    """Printed: "Machin's identity gives the rational enclosure
    pi in 16[A(5,128),A(5,129)] - 4[A(239,128),A(239,129)]" and "The Machin enclosure is rounded
    outward to 80 decimal places". The series for arctan(1/a) alternates with decreasing terms, so
    A(a,128) < arctan(1/a) < A(a,129). The difference of the two intervals is taken in interval
    arithmetic: [16 A(5,128) - 4 A(239,129), 16 A(5,129) - 4 A(239,128)]. Returns the rounded
    enclosure, which the computation uses, and the exact one."""
    n_lo, n_hi = ARCTAN_TERMS
    atan5 = Interval(arctan_partial_sum(5, n_lo), arctan_partial_sum(5, n_hi))
    atan239 = Interval(arctan_partial_sum(239, n_lo), arctan_partial_sum(239, n_hi))
    machin = atan5.times(16) - atan239.times(4)
    return machin.rounded(PI_PLACES), machin, atan5, atan239


def bernoulli_numbers(control=None):
    """Printed: "Generate the Bernoulli numbers by B_0 = 1 and
    B_m = -(m+1)^(-1) sum_{i=0}^{m-1} binom(m+1,i) B_i through m = 64"."""
    B = [Rational(1)]
    for m in range(1, BERNOULLI_LAST + 1):
        s = Rational(0)
        for i in range(m):
            s += comb(m + 1, i) * B[i]
        b = -s / (m + 1)
        if control == "C3" and m == 10:
            b = -b          # control C3 only: the recursion carries the error into B_11..B_64
        B.append(b)
    return B


def r_coefficient(B, n):
    """eq:rn: r_n = c_n (pi/2)^(2n-1) with the rational c_n = 2 (2^(2n-1) - 1) |B_2n| / (2n)!."""
    return Rational(2 * (2**(2 * n - 1) - 1), factorial(2 * n)) * abs(B[2 * n])


def r_enclosures(B, pi):
    """Printed: "substitute the enclosure of pi into (rn)". By eq:rn, r_n is a positive rational
    multiple of (pi/2)^(2n-1), so the two endpoints of the enclosure of pi give lower and upper
    bounds for r_n, n <= 32; these are rounded outward to 60 decimal places ("and the r_n
    enclosures to 60"). Returns the rounded enclosures, which the computation uses, and the
    exact ones."""
    r, r_exact = {}, {}
    for n in range(1, N_TERMS + 1):
        c = r_coefficient(B, n)
        r_exact[n] = Interval(c * (pi.lo / 2)**(2 * n - 1), c * (pi.hi / 2)**(2 * n - 1))
        r[n] = r_exact[n].rounded(R_PLACES)
    return r, r_exact


# Then the moments, the brackets of eq:finiteeseries, e_{d,k}, t_k and the loads of eq:load.

def moments(d, k):
    """Printed: "The moments follow the recursion m_0 = d/(d+1), m_j = m_{j-1}(d-k+j)/(d+j+1)",
    with moment indices 0 <= j <= 63."""
    m = [Rational(d, d + 1)]
    for j in range(1, MOMENT_LAST + 1):
        m.append(m[j - 1] * Rational(d - k + j, d + j + 1))
    return m


def bracket(d, y, m, n):
    """The n-th bracket of eq:finiteeseries, an exact rational (j = 2n - 1):
        y^j - (1 + (j+1)(j+2)/(2d)) m_j + (j(j+1)/(2d)) m_{j-1}."""
    j = 2 * n - 1
    return (y**j - (1 + Rational((j + 1) * (j + 2), 2 * d)) * m[j]
            + Rational(j * (j + 1), 2 * d) * m[j - 1])


def e_enclosure(d, k, r, T):
    """Printed: "Endpoint inclusion in these rational operations, followed by adding [-T_d,T_d],
    encloses each e_{d,k}" (eq:finiteeseries, eq:finitetail): the interval for each r_n is
    multiplied by the nth bracket and summed over n <= 32. Also returns whether the bounds behind
    eq:finitetail hold for the computed terms: "Each
    bracket is bounded in absolute value by 2 + 4n^2/(d+1), since y^j, m_j in [0,1] and
    m_j <= d/(d+1)"."""
    y = 1 - Rational(k, d)                      # "Throughout, y = 1 - k/d"
    m = moments(d, k)
    moments_ok = all(0 <= mj <= Rational(d, d + 1) for mj in m) and 0 <= y <= 1
    brackets_ok = True
    e = Interval(Rational(0), Rational(0))
    for n in range(1, N_TERMS + 1):
        c = bracket(d, y, m, n)
        if abs(c) > 2 + Rational(4 * n * n, d + 1):
            brackets_ok = False
        e = e + r[n].times(c)
    e = e + Interval(-T, T)
    return e, moments_ok, brackets_ok


def load_terms(t, d, k):
    """The expressions inside the absolute values of eq:load, enclosed by interval addition and
    subtraction: t_j + t_{k-j} - t_k for 1 <= j <= k-1 and t_k + t_{j-k} - t_j for k+1 <= j <= d-1."""
    terms = [t[j] + t[k - j] - t[k] for j in range(1, k)]
    terms += [t[k] + t[j - k] - t[j] for j in range(k + 1, d)]
    return terms


# ---------------------------------------------------------------------------------------------
# The computation for one d (run in a worker process when --jobs > 1).

_WORKER = {}


def init_worker(r_endpoints, control, details):
    _WORKER["r"] = {n: Interval(lo, hi) for n, (lo, hi) in r_endpoints.items()}
    _WORKER["control"] = control
    _WORKER["details"] = details


def compute_d(d):
    wall0, cpu0 = time.perf_counter(), time.process_time()
    r, control, details = _WORKER["r"], _WORKER["control"], _WORKER["details"]
    ks = list(range(1, d))
    T = tail_bound(d)

    # Enclosures of e_{d,k}, 1 <= k < d.
    e, moments_ok, brackets_ok = {}, True, True
    for k in ks:
        e[k], m_ok, b_ok = e_enclosure(d, k, r, T)
        moments_ok = moments_ok and m_ok
        brackets_ok = brackets_ok and b_ok

    # "the skew coefficients t_k = e_{d,d-k} - e_{d,k} and the loads l_{d,k} of (load) are enclosed
    # likewise, bounding each absolute value |[l,u]| by max(|l|,|u|)": interval addition and
    # subtraction enclose the expressions inside the absolute values of eq:load, and the sum of
    # their bounds is an upper bound for each load.
    t = {k: e[d - k] - e[k] for k in ks}
    l_hi, l_lo = {}, {}
    for k in ks:
        upper, lower = Rational(0), Rational(0)
        for x in load_terms(t, d, k):
            upper += x.abs_upper()
            lower += x.abs_lower()       # used only for the upper bound of the margin
        l_hi[k], l_lo[k] = upper, lower

    # Consistency check: the skew symmetry t_{d-k} = -t_k holds for the enclosures, and with it
    # l_{d,d-k} = l_{d,k} for the load bounds.
    symmetry_ok = all(t[d - k].lo == -t[k].hi and t[d - k].hi == -t[k].lo
                      and l_hi[d - k] == l_hi[k] and l_lo[d - k] == l_lo[k] for k in ks)

    # eq:finitecondition for each k: the lower endpoint of e and the upper bound of the load give a
    # lower bound of the left side, compared exactly with 1/(6(d+1)).
    load_factor = Rational(5, d) if control == "C2" else Rational(5, 2 * d)    # 5/(2d)
    third = Rational(1, 3 * (d + 1))
    target = Rational(1, 6 * (d + 1))
    margin_lo = {k: third + e[k].lo - load_factor * l_hi[k] for k in ks}
    margin_hi = {k: third + e[k].hi - load_factor * l_lo[k] for k in ks}
    failing_k = [k for k in ks if not margin_lo[k] >= target]

    # The normalized margin (d+1)[1/(3(d+1)) + min_k e_{d,k} - (5/(2d)) max_k l_{d,k}]. Printed
    # (caption of tab:intervals): "The margin uses lower endpoints for e_{d,k} and upper bounds for
    # l_{d,k}", which gives a lower bound. The upper endpoints for e_{d,k} and lower bounds for
    # l_{d,k} (Interval.abs_lower, summed) give an upper bound, used to locate the worst dimension.
    min_e_lo = min(e[k].lo for k in ks)
    max_l_hi = max(l_hi[k] for k in ks)
    min_e_hi = min(e[k].hi for k in ks)
    max_l_lo = max(l_lo[k] for k in ks)
    N_lo = (d + 1) * (third + min_e_lo - load_factor * max_l_hi)
    N_hi = (d + 1) * (third + min_e_hi - load_factor * max_l_lo)

    # Where min_k e_{d,k} and max_k l_{d,k} are attained. The minimum of e is located at the k
    # with the smallest lower endpoint; it is certified there when the upper endpoints of those k
    # lie below the lower endpoints of all other k. Likewise for the maximum of the loads.
    argmin_e = [k for k in ks if e[k].lo == min_e_lo]
    others = [k for k in ks if k not in argmin_e]
    argmin_e_certified = all(e[a].hi < e[b].lo for a in argmin_e for b in others)
    argmax_l = [k for k in ks if l_hi[k] == max_l_hi]
    others = [k for k in ks if k not in argmax_l]
    argmax_l_certified = all(l_hi[b] < max(l_lo[a] for a in argmax_l) for b in others)

    min_normalized_lo = (d + 1) * min(margin_lo[k] for k in ks)
    res = {
        "d": d,
        "pairs": len(ks),
        "certified": len(ks) - len(failing_k),
        "failing_k": failing_k,
        "N_lo": N_lo, "N_hi": N_hi,
        "min_e_lo": min_e_lo, "max_l_hi": max_l_hi, "min_e_hi": min_e_hi, "max_l_lo": max_l_lo,
        "T": T,
        "argmin_e": argmin_e, "argmin_e_certified": argmin_e_certified,
        "argmax_l": argmax_l, "argmax_l_certified": argmax_l_certified,
        "argmin_normalized": [k for k in ks if (d + 1) * margin_lo[k] == min_normalized_lo],
        "min_normalized_equals_N_lo": min_normalized_lo == N_lo,
        "moments_ok": moments_ok, "brackets_ok": brackets_ok, "symmetry_ok": symmetry_ok,
    }
    if details:
        per_k, digest = [], hashlib.sha256()
        names = ("e_lo", "e_hi", "t_lo", "t_hi", "load_lo", "load_hi", "margin_lo")
        for k in ks:
            strings = [exact(v) for v in (e[k].lo, e[k].hi, t[k].lo, t[k].hi,
                                          l_lo[k], l_hi[k], margin_lo[k])]
            per_k.append({
                "k": k,
                "certified": margin_lo[k] >= target,
                "e_lo": scientific(e[k].lo, "down"), "e_hi": scientific(e[k].hi, "up"),
                "t_lo": scientific(t[k].lo, "down"), "t_hi": scientific(t[k].hi, "up"),
                "load_lo": scientific(l_lo[k], "down"), "load_hi": scientific(l_hi[k], "up"),
                "margin_lo": scientific(margin_lo[k], "down"),
                "margin_hi": scientific(margin_hi[k], "up"),
                "normalized_margin_lo": fixed((d + 1) * margin_lo[k], 30, "down"),
                "sha256": {n: sha256_text(s) for n, s in zip(names, strings)},
            })
            digest.update((" ".join([str(k)] + strings) + "\n").encode("ascii"))
        res["per_k"] = per_k
        res["per_k_exact_sha256"] = digest.hexdigest()
    res["seconds"] = round(time.perf_counter() - wall0, 3)
    res["cpu_seconds"] = round(time.process_time() - cpu0, 3)
    return res


# ---------------------------------------------------------------------------------------------
# Driver: constants once, the values of d in parallel, then the assertions and the report.

def parse_args(argv):
    p = argparse.ArgumentParser(
        description="Exact rational interval computation for 2 <= d <= 65 (appendix 'Bounds on "
                    "the error coefficients', subsection 'The interval computation: proof of (ii)').")
    p.add_argument("--dmin", type=int, default=D_LOW, help="smallest d (default 2)")
    p.add_argument("--dmax", type=int, default=D_HIGH, help="largest d (default 65)")
    p.add_argument("--jobs", type=int, default=1, help="worker processes (default 1)")
    p.add_argument("--json", metavar="FILE", help="write results, exact rationals included, to FILE")
    p.add_argument("--control", choices=sorted(CONTROLS), help="a corrupted run that must fail")
    a = p.parse_args(argv)
    if not D_LOW <= a.dmin <= a.dmax <= D_HIGH:
        p.error("need 2 <= dmin <= dmax <= 65")
    if a.jobs < 1:
        p.error("need --jobs >= 1")
    return a


class Checks:
    def __init__(self):
        self.items = []

    def add(self, name, passed, detail=None):
        self.items.append({"name": name, "passed": bool(passed), "detail": detail})
        print("  %-7s %s" % ("ok" if passed else "FAILED", name))
        if detail and not passed:
            print("          " + detail)

    def failed(self):
        return [c for c in self.items if not c["passed"]]


def script_sha256():
    try:
        with open(os.path.abspath(__file__), "rb") as fh:
            return hashlib.sha256(fh.read()).hexdigest()
    except OSError:
        return "unavailable"


def fmt_ks(ks):
    return ",".join(str(k) for k in ks)


def k_words(ks):
    """[6] -> "k = 6"; [1, 6] -> "k = 1 and k = 6"; [1, 2, 3] -> "k = 1, 2 and 3"."""
    if len(ks) == 1:
        return "k = %d" % ks[0]
    if len(ks) == 2:
        return "k = %d and k = %d" % tuple(ks)
    return "k = %s and %d" % (", ".join(str(k) for k in ks[:-1]), ks[-1])


def main(argv=None):
    args = parse_args(argv)
    t_start = time.perf_counter()
    started_utc = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    ds = list(range(args.dmin, args.dmax + 1))
    n_pairs = sum(d - 1 for d in ds)
    full_range = (args.dmin, args.dmax) == (D_LOW, D_HIGH)
    jobs = min(args.jobs, len(ds))

    print("verify_coefficients.py: the exact rational interval computation of the appendix")
    print('"Bounds on the error coefficients", subsection "The interval computation: proof of (ii)", of')
    print('D. Turturean and N. Bao, "The optimal CGLMP measurements on maximally entangled states".')
    print("Script SHA-256: %s" % script_sha256())
    print("Python %s; arithmetic: %s; every endpoint is an exact rational"
          % (platform.python_version(), ARITHMETIC))
    print("Range: %d <= d <= %d (%d pairs (d,k)); worker processes: %d"
          % (args.dmin, args.dmax, n_pairs, jobs))
    if args.control:
        print("Control %s: %s. This run must fail." % (args.control, CONTROLS[args.control]))
    else:
        print("Control: none")
    print()

    checks = Checks()

    # ---- Constants, computed once.
    print("Constants")
    pi, machin, atan5, atan239 = pi_enclosure()
    checks.add("pi in 16[A(5,128),A(5,129)] - 4[A(239,128),A(239,129)]: A(a,128) < A(a,129) for "
               "a = 5, 239; enclosure width %s" % scientific(machin.hi - machin.lo, "up", 3),
               atan5.lo < atan5.hi and atan239.lo < atan239.hi and machin.lo < machin.hi)
    checks.add("the enclosure of pi rounded outward to %d decimal places contains the exact one; "
               "width %s" % (PI_PLACES, scientific(pi.hi - pi.lo, "up", 3)),
               pi.lo <= machin.lo and machin.hi <= pi.hi
               and (pi.lo * 10**PI_PLACES).denominator == 1
               and (pi.hi * 10**PI_PLACES).denominator == 1)
    lo60, hi60 = fixed(pi.lo, 60, "down"), fixed(pi.hi, 60, "down")
    checks.add("both endpoints of the pi enclosure begin with the published 60 decimals of pi "
               "(consistency check)", lo60 == PI_60_DECIMALS and hi60 == PI_60_DECIMALS,
               "%s / %s" % (lo60, hi60))

    B = bernoulli_numbers(args.control)
    wrong = [m for m, (p, q) in sorted(KNOWN_BERNOULLI.items()) if B[m] != Rational(p, q)]
    wrong_odd = [m for m in range(3, BERNOULLI_LAST + 1, 2) if B[m] != 0]
    checks.add("Bernoulli numbers B_0, ..., B_64 by the recursion: B_0, B_1, B_2, ..., B_14 and B_64 "
               "equal the published values, B_m = 0 for odd m >= 3 (consistency check)",
               not wrong and not wrong_odd,
               "differing: %s" % ", ".join("B_%d = %s" % (m, exact(B[m]))
                                           for m in sorted(wrong + wrong_odd)))

    r, r_exact = r_enclosures(B, pi)
    checks.add("r_n, 1 <= n <= 32, rounded outward to %d decimal places: each rounded enclosure "
               "contains the exact one" % R_PLACES,
               all(r[n].lo <= r_exact[n].lo and r_exact[n].hi <= r[n].hi
                   and (r[n].lo * 10**R_PLACES).denominator == 1
                   and (r[n].hi * 10**R_PLACES).denominator == 1 for n in r))
    positive = all(r_coefficient(B, n) > 0 for n in r)
    bad_r = []
    for n in r:
        four_n = Rational(1, 4**n)
        lower = 4 / pi.hi * four_n * (1 - four_n)        # (4/pi) 4^-n (1 - 4^-n)
        upper = 4 / pi.lo * four_n                       # (4/pi) 4^-n
        if not (lower < r[n].lo <= r[n].hi < upper and upper < 3 * four_n):
            bad_r.append(n)
    checks.add("r_n, 1 <= n <= 32: (4/pi) 4^-n (1 - 4^-n) < r_n < (4/pi) 4^-n < 3 4^-n, the bounds "
               "behind eq:finitetail", positive and not bad_r,
               "outside these bounds for n = %s" % fmt_ks(bad_r))

    # The closed forms: rho^-J S0(J) and rho^-J S2(J) are polynomials in J of degree 0 and 2, so
    # the telescoping identities S(J) - S(J+1) = J^p rho^J at J = 33, 34, 35 prove them for all J;
    # with S(J) -> 0 they identify S0 and S2 with the tails of sum rho^n and sum n^2 rho^n.
    tails_ok = True
    for J in (TAIL_J, TAIL_J + 1, TAIL_J + 2):
        (a0, a2), (b0, b2) = tail_sums(TAIL_RHO, J), tail_sums(TAIL_RHO, J + 1)
        tails_ok = tails_ok and a0 - b0 == TAIL_RHO**J and a2 - b2 == J * J * TAIL_RHO**J
    checks.add("closed forms of sum_{n>=J} q^n and sum_{n>=J} n^2 q^n at q = 1/4 (telescoping "
               "identity at J = 33, 34, 35); T_%d = %s, T_%d = %s"
               % (args.dmin, scientific(tail_bound(args.dmin), "up", 4),
                  args.dmax, scientific(tail_bound(args.dmax), "up", 4)), tails_ok)
    print()

    # ---- The values of d.
    r_endpoints = {n: (iv.lo, iv.hi) for n, iv in r.items()}
    details = bool(args.json)
    results = {}
    order = sorted(ds, reverse=True)          # largest d first, for load balance
    if jobs == 1:
        init_worker(r_endpoints, args.control, details)
        for d in order:
            results[d] = compute_d(d)
            sys.stderr.write("d = %d done in %.1f s (%d of %d)\n"
                             % (d, results[d]["seconds"], len(results), len(ds)))
            sys.stderr.flush()
    else:
        from concurrent.futures import ProcessPoolExecutor, as_completed
        with ProcessPoolExecutor(max_workers=jobs, initializer=init_worker,
                                 initargs=(r_endpoints, args.control, details)) as pool:
            futures = {pool.submit(compute_d, d): d for d in order}
            for fut in as_completed(futures):
                res = fut.result()
                results[res["d"]] = res
                sys.stderr.write("d = %d done in %.1f s (%d of %d)\n"
                                 % (res["d"], res["seconds"], len(results), len(ds)))
                sys.stderr.flush()

    print("Per d: N(d) is the normalized margin; its bounds are rounded outward to 30 decimals")
    print("   d  certified  lower bound of N(d)               upper bound of N(d)"
          "               min e at k  max l at k")
    for d in ds:
        x = results[d]
        print("  %2d  %3d of %2d  %s  %s  %-10s  %s"
              % (d, x["certified"], x["pairs"], fixed(x["N_lo"], 30, "down"),
                 fixed(x["N_hi"], 30, "up"), fmt_ks(x["argmin_e"]), fmt_ks(x["argmax_l"])))
    print()

    # ---- Assertions over all d.
    print("Checks for every d")
    checks.add("0 <= m_j <= d/(d+1), 0 <= y <= 1 and |bracket_n| <= 2 + 4n^2/(d+1) for n <= 32 "
               "(the bounds behind eq:finitetail)",
               all(results[d]["moments_ok"] and results[d]["brackets_ok"] for d in ds))
    checks.add("t_{d-k} = -t_k and l_{d,d-k} = l_{d,k} hold exactly for the enclosures "
               "(consistency check)", all(results[d]["symmetry_ok"] for d in ds))
    certified = sum(results[d]["certified"] for d in ds)
    failing = [(d, k) for d in ds for k in results[d]["failing_k"]]
    factor = "5/d" if args.control == "C2" else "5/(2d)"
    checks.add("eq:finitecondition: the lower bound of 1/(3(d+1)) + e_{d,k} - (%s) l_{d,k} is "
               ">= 1/(6(d+1)) for %d of %d pairs (d,k)" % (factor, certified, n_pairs),
               not failing and (n_pairs == PAIRS_FULL_RANGE or not full_range),
               "not certified at %d pairs, first (d,k) = %s" % (len(failing), failing[:12]))
    N_min = min(results[d]["N_lo"] for d in ds)
    d_min = [d for d in ds if results[d]["N_lo"] == N_min]
    if args.control == "C1":
        threshold, thr_name = N_min + Rational(1, 10**6), "the computed minimum + 10^-6"
    else:
        threshold, thr_name = MARGIN_BOUND, "1935/10^4"
    below = [d for d in ds if not results[d]["N_lo"] >= threshold]
    checks.add("normalized margin (load factor %s): the lower bound is >= %s for every d, and "
               "1935/10^4 > 1/6" % (factor, thr_name), not below and MARGIN_BOUND > ONE_SIXTH,
               "below at d = %s" % fmt_ks(below))
    print()

    wall = time.perf_counter() - t_start
    print("Run time: %.1f s wall clock with %d worker process%s"
          % (wall, jobs, "" if jobs == 1 else "es"))
    print()

    # ---- Result: the smallest normalized margin and where it occurs ("The worst dimension is
    # d = 7"). The location is certified when the upper bound at that d lies below the lower bound
    # at every other d; the decimals are those shared by the two bounds.
    print("Result for %d <= d <= %d" % (args.dmin, args.dmax))
    dm = d_min[0]
    x = results[dm]
    p_str = exact(N_min)
    num_digits = len(p_str.split("/")[0].lstrip("-"))
    den_digits = len(p_str.split("/")[1]) if "/" in p_str else 1
    print("  smallest lower bound of the normalized margin: d = %s, %s (rounded down)"
          % (fmt_ks(d_min), fixed(N_min, 30, "down")))
    print("    exact: p/q with a %d-digit p and a %d-digit q; SHA-256 of the string \"p/q\":"
          % (num_digits, den_digits))
    print("    %s" % sha256_text(p_str))
    other_lo = [results[d]["N_lo"] for d in ds if d != dm]
    located = len(d_min) == 1 and all(x["N_hi"] < v for v in other_lo)
    print("  upper bound at d = %d: %s (rounded up), %s"
          % (dm, fixed(x["N_hi"], 30, "up"),
             "below the lower bound at every other d" if located else
             "NOT below the lower bound at every other d"))
    agreed = common_decimals(x["N_lo"], x["N_hi"])
    four = fixed(x["N_lo"], 4, "down"), fixed(x["N_hi"], 4, "down")
    if located:
        print("  so the smallest normalized margin occurs at d = %d; its bounds agree on %s..."
              % (dm, agreed))
    print("  rounded down to four decimals: %s" % (four[0] if four[0] == four[1] else
                                                  "between %s and %s" % four))
    if x["argmax_l_certified"] and len(x["argmax_l"]) == 2 and sum(x["argmax_l"]) == dm:
        tie = ", where the load bounds are equal (l_{d,k} = l_{d,d-k})"
    elif x["argmax_l_certified"]:
        tie = "" if len(x["argmax_l"]) == 1 else ", where the load bounds are equal"
    else:
        tie = " (not separated from the other k)"
    print("  at d = %d: min_k e_{%d,k} is attained at %s%s;" % (
        dm, dm, k_words(x["argmin_e"]),
        "" if x["argmin_e_certified"] else " (not separated from the other k)"))
    print("    max_k l_{%d,k} at %s%s" % (dm, k_words(x["argmax_l"]), tie))

    # Comparison with the values printed in the paper.
    if full_range:
        checks.add("printed in the paper: the worst dimension for 2 <= d <= 65 is d = 7",
                   located and dm == PRINTED_D,
                   "computed: smallest lower bound at d = %s" % fmt_ks(d_min))
        checks.add("printed in the paper: the certified minimum normalized margin exceeds %s"
                   % PRINTED_MARGIN_TEXT, N_min > PRINTED_MARGIN,
                   "computed: %s" % fixed(N_min, 30, "down"))
    else:
        print("  (the worst dimension and the minimum normalized margin printed in the paper"
              " concern 2 <= d <= 65 and are not compared on this range)")

    failed = checks.failed()
    finished_utc = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    if args.json:
        write_json(args, ds, results, pi, B, r, checks, started_utc, finished_utc,
                   time.perf_counter() - t_start, jobs, N_min, d_min, threshold, located, agreed)
        print("  results written to %s" % args.json)
    if failed:
        print("FAILED: %d assertion%s did not hold (lines marked FAILED above)."
              % (len(failed), "" if len(failed) == 1 else "s"))
        return 1
    print("All assertions hold: %d of %d inequalities eq:finitecondition certified; normalized "
          "margin >= 1935/10^4 > 1/6 for %d <= d <= %d." % (certified, n_pairs, args.dmin, args.dmax))
    return 0


def write_json(args, ds, results, pi, B, r, checks, started_utc, finished_utc, wall, jobs,
               N_min, d_min, threshold, located, agreed):
    per_d = []
    for d in ds:
        x = results[d]
        row = {
            "d": d,
            "pairs": x["pairs"], "certified": x["certified"], "failing_k": x["failing_k"],
            "N_lo": fixed(x["N_lo"], 30, "down"), "N_hi": fixed(x["N_hi"], 30, "up"),
            "N_lo_ge_threshold": bool(x["N_lo"] >= threshold),
            "argmin_e": x["argmin_e"], "argmin_e_certified": x["argmin_e_certified"],
            "argmax_l": x["argmax_l"], "argmax_l_certified": x["argmax_l_certified"],
            "argmin_normalized_margin": x["argmin_normalized"],
            "min_normalized_margin_lo_equals_N_lo": x["min_normalized_equals_N_lo"],
            "T_d": scientific(x["T"], "up"),
            "exact": {k: exact(x[k]) for k in ("N_lo", "N_hi", "min_e_lo", "max_l_hi", "T")},
            "per_k_exact_sha256": x.get("per_k_exact_sha256"),
            "seconds": x["seconds"], "cpu_seconds": x["cpu_seconds"],
            "per_k": x.get("per_k"),
        }
        per_d.append(row)
    out = {
        "paper": "D. Turturean and N. Bao, The optimal CGLMP measurements on maximally entangled states",
        "computation": "appendix 'Bounds on the error coefficients', subsection 'The interval computation: "
                       "proof of (ii)'",
        "script_sha256": script_sha256(),
        "python": platform.python_version(),
        "arithmetic": ARITHMETIC,
        "platform": platform.platform(),
        "cpu_count": os.cpu_count(),
        "arguments": {"dmin": args.dmin, "dmax": args.dmax, "jobs": args.jobs, "control": args.control},
        "started_utc": started_utc, "finished_utc": finished_utc,
        "wall_seconds": round(wall, 3), "worker_processes": jobs,
        "conventions": "exact rationals are strings 'p/q'; decimals have 30 significant digits "
                       "(N: 30 decimals), lower bounds rounded down and upper bounds rounded up; "
                       "per_k[].sha256 holds the SHA-256 of each exact rational string; "
                       "per_k_exact_sha256 is the SHA-256 of the lines 'k e_lo e_hi t_lo t_hi "
                       "load_lo load_hi margin_lo' of exact rationals, k = 1, ..., d-1",
        "constants": {
            "pi_lo": exact(pi.lo), "pi_hi": exact(pi.hi),
            "bernoulli": {str(m): exact(b) for m, b in enumerate(B)},
            "r_n": [{"n": n, "lo": scientific(r[n].lo, "down"), "hi": scientific(r[n].hi, "up")}
                    for n in sorted(r)],
        },
        "per_d": per_d,
        "result": {
            "min_N_lo": {"d": d_min, "decimal": fixed(N_min, 30, "down"), "exact": exact(N_min),
                         "sha256_of_exact": sha256_text(exact(N_min))},
            "threshold": exact(threshold),
            "minimum_located": located,
            "agreed_decimals": agreed,
        },
        "checks": checks.items,
        "all_assertions_hold": not checks.failed(),
    }
    tmp = args.json + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(out, fh, indent=1)
    os.replace(tmp, args.json)


if __name__ == "__main__":
    sys.exit(main())
