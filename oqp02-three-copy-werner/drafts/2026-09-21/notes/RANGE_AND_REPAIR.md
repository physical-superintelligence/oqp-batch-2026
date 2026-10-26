# Exact range compatibility and positive repair

This is the package's acceptance proof for the range part of Proposition 6. It uses the same physical operators, trial and correction domain as the manuscript. It replaces the historical large modular transfer minor with a rank lower bound already supplied by the independently verified spectral witness. No positivity of the endpoint is assumed in proving that rank lower bound.

## 1. Spaces and one physical map

Use the invariant, complex-conjugation-averaged spaces of self-adjoint operators used by the certificate. Their native blocks are real symmetric, with the original physical Hilbert–Schmidt inner products. The resulting positive constant Grams apply to arbitrary complex physical inputs C. Write

\[
F(H)=P_hHP_h,\quad Q=I-F,\quad
\mathcal C(u_m,u_a)=\Pi_h\Gamma_m(u_m)\Pi_h+\Pi_h\Gamma_a(u_a)\Pi_h,
\qquad D=Q\mathcal C|_{\mathcal U}.
\]

The domain \(\mathcal U\) is the specified 11,149-dimensional subspace of the two supported source faces. The codomain \(Q\mathcal H_h\) has dimension 2,463. Partial transposes are full transposes on their prescribed slots before compression. Both terms act on the same common holomorphic carrier. In particular, \(\|\mathcal C\|\le\sqrt2\).

The exact geometry stage reconstructs all 720 local diagrams, both local transpose dictionaries, their physical metric isometries, and all 414 injections. The face stage computes the exact common covariance kernels; it does not select a numerical eigenspace. The coordinate stage checks every rational complementary basis, its metric orthogonality, its invertibility, the complete 2,463-coordinate quotient, and the actual target coordinates.

## 2. The 181 annihilators are physical identities over Q

The nine literal points are specified in `source/provenance/physical-kernel-completion-2026-09-17.json`, under `physical_points`. Seven are binary inputs embedded in the qutrit system, with 64 real ambient factor derivatives and one covariance each. Two are qutrit spectator zeros, with 18 real spectator derivatives and one covariance each. Thus there are 493 primary rows. Their complex phases and both adjoint shores remain in the calculation.

For each physical factorization \(C=XB\), let \(\phi_s\) denote the sector feature with integer wedge normalization. The face construction gives \(P_s\phi_s=0\) at each chosen zero. Differentiate the full feature outer-product identity, including the conjugated minor factors:

\[
\Gamma_s(\dot\phi_h\phi_h^*+\phi_h\dot\phi_h^*)
 =\dot\phi_s\phi_s^*+\phi_s\dot\phi_s^*.
\]

Sandwiching by \(P_s\) makes both terms vanish. The undifferentiated covariance has the same null property. This proves annihilation for **every signed supported Gram operator**, not just positive operators and not just the correction columns.

Let \(W\) be the common holomorphic covariance or derivative after the full local unitary, site-permutation and complex-conjugation averages. These averages preserve the defining target, supported faces and trace pairing. Therefore

\[
P_hWP_h=0,\qquad
\operatorname{Tr}(W\mathcal C u)=0,\qquad
\operatorname{Tr}(W\overline T)=0.
\]

The last equality follows from \(q(C)=0\) and its full factor derivative: the executable Gaussian-integer calculation checks both \(X^*Y=0\) and \(YB^*=0\), with \(Y=8\mathcal L_{1/2}(C)\), on all 27 coordinates. The integer feature is twice the normalized feature, so its target pairing is \(4\,d(g^2q)\), still exactly zero. No endpoint nonnegativity assumption enters this stationarity check. Outside-binary derivative directions have zero torus average; all retained real and imaginary directions are constructed before averaging. The spectator derivatives stay in the actual known zero family.

For clarity about coordinates, if \(V=UJ\), \(H=V^*V\), \(S=[K,L]\), \(H_S=S^*HS\), and \(Q_W=V^*WV\), then the trace row is formed from

\[
\nu H_S^{-1}(S^*Q_WS)H_S^{-1}.
\]

Its diagonal entries pair with diagonal target coordinates, and twice each off-diagonal entry pairs with the corresponding symmetric coordinate. The executable construction keeps both inverse metrics, the multiplicity \(\nu\), all six site permutations and the factor \(30240^{-3}\) from the local rational twirl. These are the original physical pairings.

The rational local CP factorizations are freshly reconstructed with positive rational weights and entrywise reconstruction of every charge block. Reducing their rational contractions modulo 65,521 is used **only to certify independence**. The selected primary-only 181-square minor has determinant 41,146 modulo that prime. Every denominator reduced modulo the prime is checked invertible. A nonzero reduced determinant implies a nonzero rational determinant. The executable minor selection is explicit in `checks/check_relations.py` and the referenced row/column index arrays.

Consequently the resulting map \(L:Q\mathcal H_h\to\mathbb R^{181}\) has rank 181 and

\[
LD=0,\qquad LQ\overline T=0.
\]

Writing the **complete** trial defect as
\(E=\overline T-G_h^0-\mathcal C(G_m^0,G_a^0)\), support of the trial gives \(LQE=0\). Thus \(\operatorname{rank}D\le2463-181=2282\). This implication uses the exact physical null identities above, not a congruence masquerading as an exact zero.

The detailed source derivation is `proofs/section-230dn.txt`, especially equations ZD356c–i and ZD356l. Its historical use of a separate transfer minor is replaced in this package by the next step.

## 3. Spectral data supply the matching rank lower bound

Fresh directed-rounding contractions verify all 664 blocks and give

\[
\|D-A_{48}\|_{\mathrm{op}}\le\|D-A_{48}\|_F<2^{-32}.
\]

Fresh fixed-point products and rigorous residual estimates establish

\[
\|A_{48}A_{48}^*-S_{48}\|_{\mathrm{op}}<2463\,2^{-48},
\qquad \lambda_{182}^{\uparrow}(S_{48})>2^{-30}.
\]

The increasing eigenvalue index is fixed at 182 by the checker. It is **not yet identified as a least positive eigenvalue**. Perturbation yields

\[
(s_{182}^{\uparrow}(A_{48}))^2>259681\,2^{-48},\qquad
s_{182}^{\uparrow}(D)>\sqrt{259681}\,2^{-24}-2^{-32}>127\,2^{-22}>0.
\]

Thus at least 2,282 singular values of this very same map \(D\) are positive. Combine the two rank bounds to obtain

\[
\operatorname{rank}D=2282,\qquad\operatorname{ran}D=\ker L,\qquad QE\in\operatorname{ran}D.
\]

Only now is the 182nd increasing singular value identified with the least positive singular value. The quotient coordinate changes are invertible, so the rational native relation rows and the orthonormal physical transfer describe the same range statement.

This removes any dependence on a cached assertion that an older 2,282-column minor is independent. The package retains the historical files for provenance. They do not supply this rank lower bound.

## 4. Exact positive correction, with a single defect budget

Let \(\varepsilon=2^{-35}\), \(\sigma=127\,2^{-22}\), and
\(u=D^\dagger QE\), \(v=E-\mathcal C u\). Compatibility gives \(Qv=0\). Put \(x=\|QE\|\), \(y=\|FE\|\). Before estimating, retain the orthogonal identity

\[
\|F\mathcal C u\|^2=\|\mathcal C u\|^2-\|QE\|^2
\le(2/\sigma^2-1)x^2.
\]

It follows that

\[
\|u\|<\varepsilon/\sigma,\quad
\|v\|\le y+\sqrt{2/\sigma^2-1}\,x
\le(\sqrt2/\sigma)\sqrt{x^2+y^2}<\sqrt2\varepsilon/\sigma.
\]

No defect component is spent twice. With \(b=2^{-18}\), these are \(\|u\|<(32/127)b\) and \(\|v\|<(48/127)b\). The corrected tuple

\[
G_m=G_m^0+u_m,\quad G_a=G_a^0+u_a,\quad G_h=G_h^0+v
\]

has exactly the required common target and the original supports. Its weighted margins are strictly greater than \((4016/127)b\), \((95/127)b\), \((984/127)b\) for \(h,m,a\). An empty face stays empty. Since \(\sqrt{\nu_b}\|\delta G_b\|_{\mathrm{op}}\le\|\delta G_s\|_{\mathrm{HS}}\), the bounds apply to every block with its own physical multiplicity.

## 5. Separate adversarial check of this composition

The rank lower bound is established before using rank to identify a least positive singular value. The null relations annihilate the whole supported source map, so they also annihilate its chosen subspace. They annihilate the actual target and actual trial, so they apply to the full defect. Native coordinate changes preserve both the rank and zero pairings. Complex derivatives retain conjugated minor terms and both adjoint shores. Rank-one physical inputs are covered by the manuscript's separate direct inequality, not division by a zero minor norm. Empty faces, the kernel of D, and the active endpoint are all retained. This is a documented single-author mathematical audit with executable finite checks, not independent referee approval or formal proof-assistant verification.
