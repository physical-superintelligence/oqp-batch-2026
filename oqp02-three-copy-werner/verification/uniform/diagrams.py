"""Brauer diagrams on four replicas with d as a formal parameter.

Conventions (one physical site, local dimension d, four replicas numbered 0..3):
  * P_p for p in S4 acts on (C^d)^{x4} by (P_p)_{y,x} = prod_j delta(y_{p(j)}, x_j):
    input position j goes to output position p(j).  Hence for a product vector
    r = r0 x r1 x r2 x r3,  <r, P_p r> = prod_j <r_{p(j)}, r_j>.
  * A permutation is a tuple p with p[j] = p(j).  Composition p*q = p o q (q first):
    (p*q)[j] = p[q[j]], and P_{p*q} = P_p P_q.
  * A diagram is a perfect matching on the 8 vertices ('i',j) (inputs) and ('o',j)
    (outputs), stored as a frozenset of frozensets.  P_p is the matching
    {('i',j),('o',p(j))}.  The partial transpose on a replica set T swaps the labels
    ('i',j) <-> ('o',j) for j in T.  Composition A*B (B applied first) concatenates the
    diagrams, every closed loop contributing a factor d.  The trace closes ('o',j) with
    ('i',j).  The adjoint flips 'i' <-> 'o' everywhere (real coefficients).
Elements of the algebra are dicts {diagram: polynomial in d}, polynomials being dicts
{degree: Fraction}.
"""
from fractions import Fraction
from itertools import permutations
import numpy as np

PERMS = sorted(permutations(range(4)))
IDENT = (0, 1, 2, 3)


def pmul(p, q):
    """p o q  (q first)."""
    return tuple(p[q[j]] for j in range(4))


def pinv(p):
    r = [0] * 4
    for j in range(4):
        r[p[j]] = j
    return tuple(r)


def cyc(*cycles):
    """Permutation from disjoint cycles, e.g. cyc((0,1),(2,3))."""
    p = list(range(4))
    for c in cycles:
        for k in range(len(c)):
            p[c[k]] = c[(k + 1) % len(c)]
    return tuple(p)


def perm_diagram(p):
    return frozenset(frozenset({('i', j), ('o', p[j])}) for j in range(4))


def transpose_diagram(D, T):
    """Partial transpose on replica set T: swap ('i',j)<->('o',j) for j in T."""
    T = set(T)

    def sw(v):
        s, j = v
        if j in T:
            return ('o' if s == 'i' else 'i', j)
        return v
    return frozenset(frozenset(sw(v) for v in pair) for pair in D)


def adjoint_diagram(D):
    return frozenset(frozenset(('o' if s == 'i' else 'i', j) for (s, j) in pair) for pair in D)


def compose_diagrams(A, B):
    """A*B (B first).  Returns (diagram, number_of_loops)."""
    # vertices: B inputs 'x', B outputs = A inputs 'y', A outputs 'z'; edges as a list
    edges = []
    for pair in B:
        (s1, j1), (s2, j2) = tuple(pair)
        edges.append((('x', j1) if s1 == 'i' else ('y', j1), ('x', j2) if s2 == 'i' else ('y', j2)))
    for pair in A:
        (s1, j1), (s2, j2) = tuple(pair)
        edges.append((('y', j1) if s1 == 'i' else ('z', j1), ('y', j2) if s2 == 'i' else ('z', j2)))
    inc = {}
    for k, (u, v) in enumerate(edges):
        inc.setdefault(u, []).append(k)
        inc.setdefault(v, []).append(k)
    used_edge = [False] * len(edges)
    seen_v = set()
    result = []
    loops = 0
    for v0 in list(inc):
        if v0 in seen_v:
            continue
        # traverse the component by edges
        comp_v = set()
        stack = [v0]
        comp_edges = set()
        while stack:
            u = stack.pop()
            if u in comp_v:
                continue
            comp_v.add(u)
            for k in inc[u]:
                comp_edges.add(k)
                a, b = edges[k]
                stack.append(b if a == u else a)
        seen_v |= comp_v
        ext = [v for v in comp_v if v[0] != 'y']
        if not ext:
            loops += 1
        else:
            assert len(ext) == 2, ext
            def lab(v):
                return ('i', v[1]) if v[0] == 'x' else ('o', v[1])
            result.append(frozenset({lab(ext[0]), lab(ext[1])}))
    return frozenset(result), loops


def trace_loops(D):
    """Number of loops when closing ('o',j) with ('i',j): Tr(D) = d^loops."""
    adj = {}
    for pair in D:
        a, b = tuple(pair)
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    for j in range(4):
        adj[('o', j)].append(('i', j))
        adj[('i', j)].append(('o', j))
    seen = set()
    loops = 0
    for v in adj:
        if v in seen:
            continue
        loops += 1
        stack = [v]
        while stack:
            u = stack.pop()
            if u in seen:
                continue
            seen.add(u)
            stack.extend(adj[u])
    return loops


# ---------- polynomials in d as {deg: Fraction} ----------

def padd(a, b):
    c = dict(a)
    for k, v in b.items():
        c[k] = c.get(k, Fraction(0)) + v
        if c[k] == 0:
            del c[k]
    return c


def pscale(a, s):
    return {k: v * s for k, v in a.items()} if s != 0 else {}


def pshift(a, n):
    return {k + n: v for k, v in a.items()}


def pmulpoly(a, b):
    c = {}
    for i, u in a.items():
        for j, v in b.items():
            c[i + j] = c.get(i + j, Fraction(0)) + u * v
    return {k: v for k, v in c.items() if v != 0}


def peval(a, d):
    return sum(v * Fraction(d) ** k for k, v in a.items())


# ---------- algebra elements: {diagram: poly} ----------

def elem_mul(A, B):
    C = {}
    for DA, ca in A.items():
        for DB, cb in B.items():
            D, loops = compose_diagrams(DA, DB)
            C[D] = padd(C.get(D, {}), pshift(pmulpoly(ca, cb), loops))
    return {D: c for D, c in C.items() if c}


def elem_add(A, B):
    C = dict(A)
    for D, c in B.items():
        C[D] = padd(C.get(D, {}), c)
        if not C[D]:
            del C[D]
    return C


def elem_adjoint(A):
    return {adjoint_diagram(D): c for D, c in A.items()}


def elem_trace(A):
    t = {}
    for D, c in A.items():
        t = padd(t, pshift(c, trace_loops(D)))
    return t


# ---------- explicit matrices for validation ----------

def diagram_matrix(D, d):
    """Operator on (C^d)^{x4} for a diagram: entry (y,x) = prod over pairs of deltas."""
    n = d ** 4
    M = np.zeros((n, n))
    idx = np.indices((d,) * 8).reshape(8, -1).T  # columns: y0..y3, x0..x3
    ok = np.ones(idx.shape[0], dtype=bool)
    for pair in D:
        (s1, j1), (s2, j2) = tuple(pair)
        c1 = j1 if s1 == 'o' else 4 + j1
        c2 = j2 if s2 == 'o' else 4 + j2
        ok &= idx[:, c1] == idx[:, c2]
    sel = idx[ok]
    y = np.ravel_multi_index(sel[:, :4].T, (d,) * 4)
    x = np.ravel_multi_index(sel[:, 4:].T, (d,) * 4)
    M[y, x] = 1.0
    return M


def validate_small_d(dims=(2, 3)):
    """Exhaustive check of the diagram calculus against explicit operators on (C^d)^{x4}:
    all 105 Brauer diagrams on 4+4 points (every Gamma_T(P_p)), all pairwise products with their loop
    counts, traces, adjoints, the P_p convention, the product rule P_{pq} = P_p P_q, the product-vector
    expectation <r,P_p r> = prod_j <r_{p(j)}, r_j>, and the partial-transpose convention for all p and T."""
    import random
    from itertools import combinations
    TS = [()] + [(j,) for j in range(4)] + [(a, b) for a, b in combinations(range(4), 2)] + \
         [tuple(sorted(set(range(4)) - set(c))) for c in combinations(range(4), 2)] + \
         [tuple(sorted(set(range(4)) - {j})) for j in range(4)] + [(0, 1, 2, 3)]
    diags = sorted({transpose_diagram(perm_diagram(p), T) for p in PERMS for T in TS},
                   key=lambda D: sorted(sorted(tuple(v) for v in pair) for pair in D))
    assert len(diags) == 105, len(diags)
    for d in dims:
        mats = {D: diagram_matrix(D, d) for D in diags}
        for A in diags:
            MA = mats[A]
            assert abs(np.trace(MA) - d ** trace_loops(A)) < 1e-9
            assert np.array_equal(mats[adjoint_diagram(A)], MA.T)
            for B in diags:
                C, loops = compose_diagrams(A, B)
                assert np.array_equal(MA @ mats[B], d ** loops * mats[C]), (A, B)
        for p in PERMS:
            for q in PERMS:
                assert np.array_equal(mats[perm_diagram(pmul(p, q))], mats[perm_diagram(p)] @ mats[perm_diagram(q)])
        rng = np.random.default_rng(1)
        rs = [rng.standard_normal(d) + 1j * rng.standard_normal(d) for _ in range(4)]
        r = rs[0]
        for v in rs[1:]:
            r = np.kron(r, v)
        for p in PERMS:
            lhs = np.vdot(r, mats[perm_diagram(p)] @ r)
            rhs = np.prod([np.vdot(rs[p[j]], rs[j]) for j in range(4)])
            assert abs(lhs - rhs) < 1e-9
            for T in TS:
                M = mats[perm_diagram(p)].reshape((d,) * 8)
                axes = list(range(8))
                for j in T:
                    axes[j], axes[4 + j] = axes[4 + j], axes[j]
                assert np.array_equal(M.transpose(axes).reshape(d ** 4, d ** 4), mats[transpose_diagram(perm_diagram(p), T)])
    return True


if __name__ == '__main__':
    validate_small_d()
    print('diagram calculus validated at d=2,3')
