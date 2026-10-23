# Paper to Lean

This file gives the Lean counterpart, or says that there is none, for every numbered statement and equation of
the manuscript formalized here, for its Sections 2 to 8 and Appendices A to C with the subsections 3.1, 4.3, 5.1,
6.1 and C.3, and for its Data availability statement. The manuscript is the one named in
[paper/README.md](../paper/README.md). Its theorem, equation and section numbers are those of the manuscript of
7 October 2026, which the Lean sources cite; Section 7 is now the section on the finite inputs of the two
certificates, and the objects removed since 7 October are listed at the end of this file. The manuscript proves
Theorem 2.1 and Corollary 2.2 for `d = 3` and `d = 4`; the formalization covers the qutrit case `d = 3`, three
copies. Where a row states a result for both dimensions, its Lean cell gives the `d = 3` part, and the `d = 4`
part is not formalized.

Lean names are in the namespace `ThreeCopyQutritWerner`. `Endpoints.` marks the 48 theorems stated in
[`Challenge.lean`](../Challenge.lean) and proved in [`Solution.lean`](../Solution.lean); their statements in words
are in [FIDELITY.md](FIDELITY.md). The other names are definitions and theorems of the library
`ThreeCopyQutritWerner/`.

## Numbered statements and equations

### Section 1

| Manuscript | Content | Lean |
|---|---|---|
| eq. (1) | the Werner state `ρ_{d,α} = (I − α F^{(d)})/(d(d − α))`, `−1 ≤ α ≤ 1` | `werner` (defined for every real α; each theorem states its range of α), `swapOp` (the flip); `Endpoints.werner_state` (a state for −1 ≤ α ≤ 1 and d ≥ 2) |

### Section 2

| Manuscript | Content | Lean |
|---|---|---|
| Section 2 | the sharp three-copy minimum and the threshold: `n`-copy distillability, the Schmidt-rank-two criterion, the energy `q_α`, and the results for `d = 3` and `d = 4` | the rows below, for d = 3; distillability of one and of three copies is `IsOneCopyFilterDistillable` and `IsThreeCopyFilterDistillable` (local filters onto two qubits), and the Schmidt-rank-two criterion is `Endpoints.filter_iff_rank_two_detectable`; d = 4: not formalized |
| eq. (2) | `N`, `A`, `B`, `T₀` of a matrix `C` on three sites, with unnormalized partial traces | `invN`, `invA`, `invB`, `invT`, with `frobSq` and `ptrace₁`, `ptrace₂`, `ptrace₃`, `ptrace₁₂`, `ptrace₁₃`, `ptrace₂₃` |
| eq. (3) | `q_α(C) = N − αA + α²B − α³T₀` and `q = q_{1/2}` | `energy`, `endpointEnergy` |
| Theorem 2.1 | sharp three-copy minimum for `d = 3, 4`, the interior minimizers, and unequal local dimensions `2 ≤ dᵢ ≤ 4` | for d = 3: `Endpoints.qutritEndpointInequality` (q(C) ≥ 0 on rank at most two, the endpoint α = 1/2), `Endpoints.sharp_minimum` (eq. (4)), `Endpoints.interior_minimizers` (eq. (5)), `Endpoints.minimum_formula_unequal_dims` (unequal local dimensions, the case 2 ≤ dᵢ ≤ 3); d = 4 and local dimension 4: not formalized |
| eq. (4) | `m_{3,d}(α) = (1 − 2α)(1 − α)²` for `0 ≤ α ≤ 1/2`, `d = 3, 4` | for d = 3: `sharpCurve`; `Endpoints.sharp_minimum`, with `Endpoints.sharp_curve_attained` (attainment) and `Endpoints.sharp_minimum_isLeast_of_endpoint` (the minimum as a least value); d = 4: not formalized |
| eq. (5) | the interior minimizers `e^{iθ} P_E/√2 ⊗ \|u⟩⟨u\| ⊗ \|v⟩⟨v\|`, up to a permutation of the sites | for d = 3: `IsInteriorMinimizerShape`; `Endpoints.interior_minimizers`, with `Endpoints.interior_shape_attains` (every such matrix attains the curve); d = 4: not formalized |
| eq. (6) | `⟨vec C, (ρ^Γ)^{⊗3} vec C⟩ = q_α(C)/[d(d − α)]³` and `SR(vec C) = rank C` | `Endpoints.three_copy_expectation` (the expectation identity, every d), `Endpoints.schmidtRank_vec` (SR(vec C) = rank C), with `vec`, `expectation`, `partialTranspose`, `tripleCopy`, `SchmidtRankLE` |
| Corollary 2.2 | for `d = 3, 4`: three copies are distillable exactly for `α > 1/2`; NPT and three-copy nondistillable for `1/d < α ≤ 1/2`; for `α ≤ 1/2`, every trace-preserving separable operation from three copies to two qubits, such as a deterministic two-way LOCC map, has output overlap at most `1/2` with a maximally entangled state | for d = 3: `Endpoints.werner_three_three_copy_iff` (for α ≤ 1), `Endpoints.werner_three_npt_not_three_copy`, `Endpoints.overlap_le_half` (the overlap claim for the same class of operations, 0 ≤ α ≤ 1/2); distillability is the local-filter notion `IsThreeCopyFilterDistillable`, and the Schmidt-rank-two criterion of the proof is `Endpoints.filter_iff_rank_two_detectable`; d = 4: not formalized |

### Section 3

| Manuscript | Content | Lean |
|---|---|---|
| Section 3 | the reduction of Theorem 2.1 to its endpoint | the rows below; the implications from the endpoint inequality: `Endpoints.sharp_minimum_of_endpoint`, `Endpoints.interior_minimizers_of_endpoint`, `Endpoints.minimum_formula_of_card_of_endpoint` |
| eq. (7) | `R(C) = N − T₀/2` and `S(C) = N − (A + B)/6 + T₀/4`, both nonnegative on rank at most two | `formR`, `formS`; `Endpoints.formR_nonneg_rank_two`, `Endpoints.cutForms_nonneg_rank_two` (S ≥ 0 among them) |
| eq. (8) | the cut forms `Q_i(C) ≥ 0` | `cutForm₁`, `cutForm₂`, `cutForm₃`; `Endpoints.cutForms_nonneg_rank_two` |
| Proposition 3.1 | exact continuation | `Endpoints.continuation_identity` |
| eq. (9) | `q_α − f(α)N = (4α(1 + α)/3) q + α(1 − 2α)(2/3 − α) R + 2α(1 − 2α) S` | `Endpoints.continuation_identity`, with `sharpCurve` for f |
| Section 3.1 | classification of the interior minimizers: the proof of the equality statement of Theorem 2.1 | `Endpoints.interior_minimizers_of_endpoint` (the equality statement for d = 3, from the endpoint inequality), with `Endpoints.two_plane_product` (Step 4: the two-plane factor sits at one site) |
| eq. (10) | `R(C) = ‖C − (Tr C) P/2‖_F²` for a rank-two projection `P` with `PC = C` | `Endpoints.formR_eq_proj` |
| eq. (11) | the cut identity for the projection onto a two-plane | `Endpoints.projector_cut_identity` (two-factor form), `Endpoints.cutForm_two_plane_projector` (right-hand side), with `biDefect` and `cutForm` |

### Section 4

| Manuscript | Content | Lean |
|---|---|---|
| Section 4 | the exact positive certificate for the endpoint | `Endpoints.qutrit_endpoint_of_certificate` (Section 4.1: a certificate of the form (14) implies the endpoint inequality); the certificate of the formal proof is described below, under the route of the formal proof |
| eq. (12) | the features `z_h`, `z_m`, `z_a` built from `C = X Y†` and the bivector `p` of the columns of `X` | `featureH`, `featureM`, `featureA`, with `bivecMat` for p (the Lean statements write C as X * B) |
| eq. (13) | the carrier projections `Π_h`, `Π_m`, `Π_a` | `certificateQutritCarrier` (Π_h; its factor on the first five registers is Π_(3,2) Alt₁₂ Alt₃₄ by `certificateHolomorphicCarrier_eq`; it fixes every z_h by `certificateQutritCarrier_fixes`); `certificateMixedCarrier` (the action of Π_m, which fixes z_m by `certificateMixedCarrier_feature`); the Π_(2,2) action that fixes z_a, `certificateCentralAction_conj_bivec_square` |
| eq. (14) | the certificate equation `Θ_h = G_h + B_m(G_m) + B_a(G_a)`, with `Θ_h = Π_h Θ Π_h` and `G_s = Π_s G_s Π_s ⪰ 0` | the hypothesis of `Endpoints.qutrit_endpoint_of_certificate` (without the support conditions), with `sixRegisterOperator` (Θ on the six registers), `partialTranspose` (Γ₃₄) and `minorTranspose` (Γ₁₂₃₄); the formal proof uses it through `qutritEndpointInequality_of_explicit_carrier_certificate` and `qutritEndpointInequality_of_exact_residual` |
| eq. (15) | `g² q(C) = z_h† G_h z_h + z_m† G_m z_m + z_a† G_a z_a ≥ 0` | `featureH_soundness` |
| eq. (16) | the full residual `Δ` of a trial tuple | `certificateExactTrialDefect` |
| eq. (17) | the repair map `D` | no Lean counterpart; the formal proof uses no repair map |
| Lemma 4.1 | exact supported repair | no Lean counterpart in the formal proof, which checks the identity (14) with an exact correction instead (README, proof outline); the identity part of the lemma is stated in the library as `certificateExactResidual_repair` |
| eq. (18) | the repaired tuple | the correction δ_h: `certificateExactHolomorphicCorrection`; the choice δ = D⁺QΔ has no Lean counterpart |
| eq. (19) | the bounds on the corrections | no Lean counterpart; the formal proof uses no error bound |
| Section 4.3 | the qutrit and ququart certificates | the rational trial tuple of the qutrit certificate is part of the data of the formal proof, which replaces the correction (20) by an exact correction of its own (README, proof outline); the ququart certificate (d = 4): not formalized |
| eq. (20) | the rational correction `c = W⁻¹D_Iᵀ(D_I W⁻¹ D_Iᵀ)⁻¹Δ_I` | no Lean counterpart; the formal proof checks the identity (14) with an exact correction instead (README, proof outline); the correction of the formal proof solves the same coefficient equations |

### Section 5

| Manuscript | Content | Lean |
|---|---|---|
| Section 5 | the qutrit endpoint zeros | the rows below and Appendix C; `Endpoints.endpoint_zero_rank_two` (every nonzero endpoint zero has rank two) |
| eq. (21) | family I: `P_E/√2 ⊗ \|χ⟩⟨η\|` is a normalized endpoint zero | `familyIMat`; `Endpoints.familyI_endpoint_zero_any_plane` |
| Theorem 5.1 | qutrit endpoint equality: the normalized zeros of rank at most two are exactly the members of families I–III | the inclusion of the families in the zero set, with both singular values 1/√2: `Endpoints.zero_families_are_half_singular_zeros`; the converse inclusion, path-connectedness and the dimensions 36 and 12: no Lean counterpart |
| eq. (22) | the families I, II and III | `familyIMat`, `familyII`, `familyIII`, `IsQutritZeroFamilyMember`, with `epsMat`, `binaryB₂`, `binaryB₃` |
| Section 5.1 | proof of the classification from the certificate kernel | `Endpoints.endpoint_zero_rank_two` (Step 2: every nonzero endpoint zero has rank two); the zero relations and the analytic inputs: the rows of eq. (24) and Appendix C; the converse inclusion as a whole: no Lean counterpart (row of Theorem 5.1) |
| eq. (23) | `H(C, p) = (Cp − pCᵀ)/2`: symmetric, of rank at most two, with range in the range of `C` | `hFeature`; `hFeature_transpose`, `rank_hFeature_le`, `hFeature_eq_mul` |
| eq. (24) | the zero relations `(Alt_j Alt_k H(C, p)) ⊗ (Alt_i p) = 0` | `ZeroRelations`; `zeroRelationMap₁`, `zeroRelationMap₂`, `zeroRelationMap₃` (the three linear maps on z_h) |

### Section 6

| Manuscript | Content | Lean |
|---|---|---|
| Section 6 | consequences in larger dimensions | the rows below |
| Section 6.1 | endpoint positivity for local overlaps of rank at most four | not formalized (it rests on Theorem 2.1 at d = 4) |
| Theorem 6.1 | endpoint extension by local overlap: `q(C) ≥ 0` and `q_α(C) ≥ f(α)‖C‖_F²` (`0 ≤ α ≤ 1/2`) for `rank C ≤ 2` with local overlaps of rank at most four at all three sites | not formalized (its proof uses Theorem 2.1 at d = 4) |
| eq. (25) | the conclusion of Theorem 6.1 | not formalized |
| eq. (26) | the splitting identity for one local overlap, in the proof of Theorem 6.1 | not formalized |
| eq. (27) | `ρ̃_d = (V ⊗ V) ρ_{3,1/2} (V ⊗ V)†` and `τ_{d,t} = t ρ̃_d + (1 − t) I/d²`, for an isometry `V : ℂ³ → ℂ^d`, `d ≥ 3` | `embedPair`, `noisyFamily` (whose arguments J and p are V and t) |
| Corollary 6.2 | for `d ≥ 3` and `15/(d² + 15) < t < 1`, `τ_{d,t}` is full rank, NPT and nondistillable through three copies | `Endpoints.noisy_family_posDef` (full rank), `Endpoints.noisy_family_npt` (NPT), `Endpoints.noisy_family_three_copy_of_endpoint` (three-copy nondistillability from the endpoint inequality, which `Endpoints.qutritEndpointInequality` proves) |
| eq. (28) | the threshold `15/(d² + 15) < t < 1` | the hypotheses on p of `Endpoints.noisy_family_npt` and `Endpoints.noisy_family_three_copy_of_endpoint` |

### Section 7

| Manuscript | Content | Lean |
|---|---|---|
| Section 7 | finite inputs of the qutrit and ququart certificates | no Lean counterpart; the formal proof uses its own certificate data, which the kernel checks (README, proof outline); the d = 4 inputs: not formalized |
| Proposition 7.1 | finite inputs for `d = 3` and `d = 4`, items (i) to (v): the relations `L`, the face margins and the residual bound, the approximation of `D`, the eigenvalue bound, and the faces as kernels | no Lean counterpart; the formal proof checks the identity (14) with an exact correction instead (README, proof outline), and uses none of these bounds; the d = 4 items: not formalized |
| Lemma 7.2 | rank and gap of the repair map, for `d = 3` and `d = 4` | no Lean counterpart; the formal proof uses no repair map; d = 4: not formalized |

### Section 8

| Manuscript | Content | Lean |
|---|---|---|
| Section 8 | open problems beyond ququarts and three copies | no Lean counterpart |

### Appendices

| Manuscript | Content | Lean |
|---|---|---|
| Appendix A | the two-copy rank-two inequality as a sum of squares | `Endpoints.cutForms_nonneg_rank_two`; `cutForm_nonneg_of_balanced` |
| eq. (29) | `Q_Λ(C) = (ℓ₁ − ℓ₂)²/2 + \|ℓ₁₂\|² + (e_X + e_Y + e₁ + e₂ + ‖𝒯(M)‖²)/2 ≥ 0`, with `M = x₂x₁† − y₂y₁†` | `cutForm_nonneg_of_balanced` (balanced factors), with `biDefect` |
| Appendix B | character formulas for the feature projectors | `certificateCharacter` (the character), `certificateHolomorphicCarrier_eq`, `certificateCentralAction_column_bivec_square` (the Π_(3,2) projection fixes a source column with two equal decomposable bivectors) |
| Appendix C | the analytic inputs of the qutrit zero classification | `Endpoints.appendixC_input1`, `Endpoints.appendixC_input2`, `Endpoints.appendixC_input3`; the formula for H: `hFeature_formula` |
| Appendix C.3 | classification of the zeros with a thin range: the proof of input 3 | `Endpoints.appendixC_input3` |

### Data availability

| Manuscript | Content | Lean |
|---|---|---|
| Data availability (unnumbered) | the supplement: the rational data of the qutrit and ququart certificates and a checker | no Lean counterpart; the formal proof uses its own certificate data under verification/, which the kernel checks (README, proof outline) |

## The route of the formal proof

The formal proof of the endpoint inequality, `Endpoints.qutritEndpointInequality` (through
`x2_qutritEndpointInequality`), uses a certificate of the form of Section 4.1, eq. (14): the manuscript's rational
trial tuple together with an exact rational correction on eight blocks that solves the coefficient equations
exactly. It does not use the repair of Lemma 4.1, the bounds (19), the finite inputs of Proposition 7.1 and
Lemma 7.2 or the correction of eq. (20): G_h is the exact residual of the corrected tuple, and the Lean kernel
checks every identity and the positivity of every block, so no floating-point or interval bound enters the proof
(README, proof outline).

## Theorems of record without a numbered item of their own

| Lean theorem | Statement (from FIDELITY.md) |
|---|---|
| `Endpoints.werner_npt_iff` | Section 1: NPT exactly when α > 1/d. |
| `Endpoints.werner_three_one_copy_iff` | Section 1: one-copy distillable exactly when α > 1/2 (d = 3). |
| `Endpoints.werner_three_three_copy_of_gt` | Corollary 2.2: distillable for 1/2 < α (d = 3). |
| `Endpoints.werner_three_not_three_copy_of_nonpos` | Corollary 2.2 proof: α ≤ 0 (d = 3). |
| `Endpoints.werner_three_not_three_copy_of_le_third` | Corollary 2.2 at `d = 3`, PPT region: for `α ≤ 1/3` three copies are not distillable (the state has positive partial transpose there). |
| `Endpoints.overlap_le_half_of_nonpos` | Corollary 2.2, separable operations, α ≤ 0 (d = 3). |
| `Endpoints.overlap_le_half_of_le_third` | Corollary 2.2, separable operations, PPT region `α ≤ 1/3` (`d = 3`). |
| `Endpoints.werner_three_three_copy_iff_of_endpoint` | Implication T2.1a ⇒ C2.2a. |
| `Endpoints.werner_three_npt_not_three_copy_of_endpoint` | Implication T2.1a ⇒ C2.2b. |
| `Endpoints.overlap_le_half_of_endpoint` | Implication T2.1a ⇒ C2.2c (separable operations). |
| `Endpoints.rank_raise_ptrace` | Section 1 (`d = 3`): the partial trace over site 1 of a coefficient matrix of rank at most two can have rank three. |
| `Endpoints.three_copy_ppt_of_le_third` | PPT region (`d = 3`, `α ≤ 1/3`): the partial transpose of three copies of the Werner state is positive semidefinite, so no vector of any Schmidt rank detects three copies. |
| `Endpoints.werner_two_half_separable` | Section 1 and the proof of Corollary 2.2 (Steps 1 and 5), at `d = 2`: the qubit Werner state at `α = 1/2` is separable (for `α ≤ 1` it is NPT exactly when `α > 1/2`, `werner_npt_iff` at `d = 2`). |
| `Endpoints.twoQubit_separable_iff_ppt` | Peres–Horodecki two-qubit criterion, quoted in the proof of Corollary 2.2: a two-qubit operator is separable (a finite nonnegative combination of products of positive semidefinite operators, the zero operator included) exactly when it and its partial transpose are positive semidefinite. |

## Removed since the manuscript of 7 October 2026

| Manuscript of 7 October 2026 | Content | Now |
|---|---|---|
| Table 1 | quantitative inputs to the repair lemma | removed: its numbers are stated once, in Proposition 7.1, Lemma 7.2 and the corrected margins at the end of Section 7 |
| Section 7 of 7 October | how the two certificates fit together | removed: Section 7 now holds the finite inputs of both certificates (rows above) |
| Appendix D | certificate evidence and reproducibility | removed: the finite inputs are in Section 7 (Proposition 7.1, Lemma 7.2), and the data and the checker's command are in the Data availability statement |
