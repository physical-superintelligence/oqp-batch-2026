# Statement fidelity

This file maps the notions and results of the manuscript *Three-copy nondistillability of qutrit and
ququart Werner states* (Physical Superintelligence (PSI), manuscript of 21 October 2026; see
[paper/README.md](../paper/README.md)) to the definitions and theorems of
[`Challenge.lean`](../Challenge.lean). All Lean names below are in the namespace `ThreeCopyQutritWerner`;
the 48 theorems listed in `comparator.json` are in `ThreeCopyQutritWerner.Endpoints`.
[docs/PAPER_TO_LEAN.md](PAPER_TO_LEAN.md) gives, for every numbered statement and equation of the
manuscript, its Lean counterpart or says that it has none.

The manuscript proves Theorem 2.1 and Corollary 2.2 for local dimensions `d = 3` and `d = 4`; this repository
formalizes the qutrit case `d = 3`. Of Theorem 5.1, the theorems of record contain the inclusion ⊇ with the
singular values (`zero_families_are_half_singular_zeros`) and, for the inclusion ⊆, its rank-two step and the
three analytic inputs of Appendix C (`endpoint_zero_rank_two`, `appendixC_input1` to `appendixC_input3`).

## Definitions

| Manuscript | Lean (`ThreeCopyQutritWerner/Basic.lean`) |
|---|---|
| the Werner state `ρ_{d,α} = (I − α F^{(d)})/(d (d − α))`, eq. (1) | `werner d α` (total in `α`; each theorem states its range of `α`) |
| the flip `F^{(d)} (u ⊗ v) = v ⊗ u` and `Ω^{(d)} = \|Ω^{(d)}⟩⟨Ω^{(d)}\|`, `\|Ω^{(d)}⟩ = Σⱼ \|jj⟩` | `swapOp`, `omegaOp` |
| partial transpose `ρ^Γ` (on the second factor) | `partialTranspose` |
| three copies `ρ^{⊗3}` across the cut `A₁A₂A₃ \| B₁B₂B₃` | `tripleCopy` |
| test vector `vec C` of a coefficient matrix `C` (row-first) and `⟨ψ, M ψ⟩` | `vec`, `expectation` |
| Schmidt rank at most `r` | `SchmidtRankLE r` |
| NPT: the partial transpose is not positive semidefinite | `IsNPT` |
| `N = ‖C‖_F²`, `A = Σᵢ ‖Trᵢ C‖_F²`, `B = Σ_{i<j} ‖Tr_{ij} C‖_F²`, `T₀ = \|Tr C\|²`, eq. (2) | `invN`, `invA`, `invB`, `invT` (unnormalized partial traces `ptrace₁`, …, `ptrace₂₃`) |
| `q_α(C) = N − α A + α² B − α³ T₀` and `q = q_{1/2}`, eq. (3) | `energy α`, `endpointEnergy` |
| the sharp curve `f(α) = (1 − 2α)(1 − α)²`, eq. (4) | `sharpCurve` |
| `R`, `S`, eq. (7); the cut forms `Q₁, Q₂, Q₃`, eq. (8) | `formR`, `formS`, `cutForm₁`, `cutForm₂`, `cutForm₃` |
| the shape of eq. (5), up to a permutation of the sites | `IsInteriorMinimizerShape` |
| T2.1a: `q(C) ≥ 0` for every complex `27 × 27` matrix of rank at most two | `QutritEndpointInequality` |
| distillability of one, respectively three, copies: some local filters onto two qubits give an NPT operator | `IsOneCopyFilterDistillable`, `IsThreeCopyFilterDistillable` (with `localFilter`) |
| detection by a vector of Schmidt rank at most two | `IsOneCopyRankTwoDetectable`, `IsThreeCopyRankTwoDetectable` |
| the overlap claim of Corollary 2.2: overlap with the maximally entangled two-qubit state of the output of a trace-preserving separable operation on three copies | `maxEntOverlap (sepOutput A B ρ)`, with the trace-preservation condition `htp` on the Kraus pairs `(A k, B k)` |
| separability of a bipartite operator | `IsBipartiteSeparable` |
| the families I–III of Theorem 5.1, at every site placement, times a unit phase | `familyIMat`, `familyII`, `familyIII`, `IsQutritZeroFamilyMember` |
| the full-rank family of eq. (27) and Corollary 6.2: the qutrit endpoint state embedded by an isometry `V : ℂ³ → ℂᵈ` and mixed with white noise, `τ_{d,t} = t ρ̃_d + (1 − t) I/d²` with `ρ̃_d = (V ⊗ V) ρ_{3,1/2} (V ⊗ V)†` | `noisyFamily J p = p (J ⊗ J) ρ_{3,1/2} (J ⊗ J)† + (1 − p) I/d²` (with `embedPair`; `J` and `p` are the manuscript's `V` and `t`) |
| the certificate objects of Section 4.1: six registers, the feature `z_h`, the bivector matrix of `X`, `Θ` (the identity on registers 1 to 4), `Γ₃₄`, `Γ₁₂₃₄` | `SixRegisters`, `featureH`, `bivecMat`, `sixRegisterOperator`, `partialTranspose`, `minorTranspose` |
| the two-factor forms of eq. (11) | `cutForm`, `ptraceNormSq`, `biDefect` (with `ptraceL`, `ptraceR`, `ketBra`, `braket`, `vecNormSq`, `tensor₂`, `tensor₃`) |

## Conventions

- Matrices are complex; a three-site operator is a matrix indexed by `a × b × c` and need not be
  Hermitian or normal. Partial traces are unnormalized, and `frobSq` is the squared Frobenius norm.
- The partial transpose acts on the second tensor factor. A test vector on `A₁A₂A₃ | B₁B₂B₃` is the
  row-first vectorization of a matrix whose rows are indexed by Alice's three sites and columns by Bob's.
- "Distillable" is the operational local-filter notion: one (or three) copies are distillable when some
  local filters onto two qubits give an NPT operator. For Hermitian states this is equivalent to detection
  by a vector of Schmidt rank at most two (`filter_iff_rank_two_detectable`).
- The overlap claim of Corollary 2.2 is stated for trace-preserving separable operations from three copies
  to two qubits, `ρ ↦ Σ_k (A_k ⊗ B_k) ρ^{⊗3} (A_k ⊗ B_k)†`, among them the deterministic two-way LOCC maps
  (that inclusion is not formalized). For `α ≤ 1/2` it is covered by `overlap_le_half` (`0 ≤ α ≤ 1/2`) and
  `overlap_le_half_of_nonpos` (`α ≤ 0`).
- `werner d α` is defined for every real `α`; each theorem states the range of `α` it covers (for example
  `-1 ≤ α ≤ 1` in `werner_state`, `α ≤ 1` in `werner_three_three_copy_iff`, `0 ≤ α ≤ 1/2` in
  `sharp_minimum` and `overlap_le_half`).
- A theorem with no lower bound on `α` (`werner_npt_iff`, `werner_three_three_copy_iff` and its
  `_of_endpoint` form, `werner_three_not_three_copy_of_nonpos`, `werner_three_not_three_copy_of_le_third`,
  `three_copy_ppt_of_le_third`, `overlap_le_half_of_nonpos`, `overlap_le_half_of_le_third`) also covers
  `α < -1`. There `werner d α` has trace one and is not positive semidefinite, but its partial transpose is
  positive semidefinite, which is why these statements hold there too. Every theorem about `werner d α`
  except the identity `three_copy_expectation` assumes `α ≤ 1`, so none admits `α = d`, where Lean's
  `0⁻¹ = 0` gives `werner d d = 0`; `three_copy_expectation` holds for every real `α`, at `α = d` with both
  sides zero.
- The hypotheses of each theorem are exactly those in its statement. `comparator.json` permits exactly the
  axioms `propext`, `Quot.sound` and `Classical.choice`.

## The statements of record

| Lean theorem (`Endpoints.…`) | Manuscript statement |
|---|---|
| `qutritEndpointInequality` | Theorem 2.1 of the manuscript at `d = 3`, `α = 1/2` (claim T2.1a), the qutrit endpoint inequality: `q(C) ≥ 0` for every complex `27 × 27` matrix `C` of rank at most two, where `q = endpointEnergy` is the three-copy form `q_{1/2}` (`QutritEndpointInequality`). |
| `sharp_minimum` | Theorem 2.1, eq. (4), at `d = 3` (claim T2.1b): for `0 ≤ α ≤ 1/2`, `q_α(C) ≥ (1 - 2α)(1 - α)² ‖C‖_F²` for every matrix of rank at most two, with equality for some normalized matrix of rank at most two. |
| `interior_minimizers` | Theorem 2.1, eq. (5), at `d = 3` (claim T2.1c): for `0 < α < 1/2`, every normalized minimizer of `q_α` over rank at most two has the shape of eq. (5) up to a permutation of the sites. |
| `minimum_formula_unequal_dims` | Theorem 2.1, unequal dimensions, the case `2 ≤ dᵢ ≤ 3` (claim T2.1d): for `0 ≤ α ≤ 1/2`, `q_α(C) ≥ (1 - 2α)(1 - α)² ‖C‖_F²` for every matrix of rank at most two on sites of dimensions `2 ≤ dᵢ ≤ 3`, with equality for some normalized matrix of rank at most two. |
| `werner_three_three_copy_iff` | Corollary 2.2 at `d = 3` (claim C2.2a): for `α ≤ 1`, three copies of the qutrit Werner state are distillable exactly when `α > 1/2`. |
| `werner_three_npt_not_three_copy` | Corollary 2.2 at `d = 3` (claim C2.2b): for `1/3 < α ≤ 1/2` the qutrit Werner state is NPT and three copies of it are not distillable. |
| `overlap_le_half` | Corollary 2.2, at `d = 3` (claim C2.2c): for `0 ≤ α ≤ 1/2`, every trace-preserving separable operation from three copies of the qutrit Werner state to two qubits outputs an operator whose overlap with the maximally entangled state is at most `1/2`. |
| `continuation_identity` | Proposition 3.1, eq. (9). |
| `formR_nonneg_rank_two` | Section 3, eq. (7): R ≥ 0 on rank at most two. |
| `cutForms_nonneg_rank_two` | Section 3, eq. (8) and Appendix A: Q₁, Q₂, Q₃, S ≥ 0 on rank at most two. |
| `three_copy_expectation` | eq. (6), the expectation identity. |
| `schmidtRank_vec` | eq. (6): SR(vec C) = rank C. |
| `werner_state` | eq. (1): the Werner state. |
| `werner_npt_iff` | Section 1: NPT exactly when α > 1/d. |
| `werner_three_one_copy_iff` | Section 1: one-copy distillable exactly when α > 1/2 (d = 3). |
| `werner_three_three_copy_of_gt` | Corollary 2.2: distillable for 1/2 < α (d = 3). |
| `werner_three_not_three_copy_of_nonpos` | Corollary 2.2 proof: α ≤ 0 (d = 3). |
| `werner_three_not_three_copy_of_le_third` | Corollary 2.2 at `d = 3`, PPT region: for `α ≤ 1/3` three copies are not distillable (the state has positive partial transpose there). |
| `interior_shape_attains` | Section 3: every matrix of the shape (5) attains the sharp curve. |
| `familyI_endpoint_zero_any_plane` | eq. (21) (family I of Theorem 5.1, site 1 active): for every two-plane `E = span(f₁, f₂)` (orthonormal pair) and unit `χ`, `η` on sites 2 and 3, `(P_E/√2) ⊗ \|χ⟩⟨η\|` is a normalized endpoint zero of rank at most two, in any finite local dimensions. |
| `endpoint_zero_rank_two` | Section 5.1: every nonzero endpoint zero has rank two. |
| `overlap_le_half_of_nonpos` | Corollary 2.2, separable operations, α ≤ 0 (d = 3). |
| `overlap_le_half_of_le_third` | Corollary 2.2, separable operations, PPT region `α ≤ 1/3` (`d = 3`). |
| `filter_iff_rank_two_detectable` | The rank-two filter criterion: for Hermitian `ρ`, one (respectively three) copies are distillable by local filters onto two qubits exactly when some vector of Schmidt rank at most two has negative expectation in the partial transpose of `ρ` (respectively of `ρ^{⊗3}`). |
| `sharp_curve_attained` | Theorem 2.1, eq. (4), attainment (`d = 3`): for every real `α` a normalized matrix of rank at most two attains the sharp curve. |
| `sharp_minimum_of_endpoint` | Implication T2.1a ⇒ T2.1b. |
| `minimum_formula_of_card_of_endpoint` | Implication from T2.1a: Theorem 2.1, unequal dimensions, the case `2 ≤ dᵢ ≤ 3`. |
| `interior_minimizers_of_endpoint` | Implication T2.1a ⇒ T2.1c. |
| `werner_three_three_copy_iff_of_endpoint` | Implication T2.1a ⇒ C2.2a. |
| `werner_three_npt_not_three_copy_of_endpoint` | Implication T2.1a ⇒ C2.2b. |
| `overlap_le_half_of_endpoint` | Implication T2.1a ⇒ C2.2c (separable operations). |
| `formR_eq_proj` | Section 3.1, eq. (10): for a Hermitian projector `P` of trace two with `P C = C`, `R(C) = ‖C - (Tr C) P / 2‖_F²`. |
| `rank_raise_ptrace` | Section 1 (`d = 3`): the partial trace over site 1 of a coefficient matrix of rank at most two can have rank three. |
| `three_copy_ppt_of_le_third` | PPT region (`d = 3`, `α ≤ 1/3`): the partial transpose of three copies of the Werner state is positive semidefinite, so no vector of any Schmidt rank detects three copies. |
| `werner_two_half_separable` | Section 1 and the proof of Corollary 2.2 (Steps 1 and 5), at `d = 2`: the qubit Werner state at `α = 1/2` is separable (for `α ≤ 1` it is NPT exactly when `α > 1/2`, `werner_npt_iff` at `d = 2`). |
| `noisy_family_posDef` | Corollary 6.2: `noisyFamily J p` has full rank for `0 ≤ p < 1`. |
| `noisy_family_npt` | Corollary 6.2: for an isometry `J : ℂ³ → ℂᵈ`, `noisyFamily J p` is NPT for `15/(d² + 15) < p ≤ 1`. (Its three-copy nondistillability follows from T2.1a: `noisy_family_three_copy_of_endpoint`.) |
| `sharp_minimum_isLeast_of_endpoint` | Implication from T2.1a: Theorem 2.1, eq. (4), as an attained minimum (`IsLeast`) over normalized matrices of rank at most two. |
| `zero_families_are_half_singular_zeros` | Theorem 5.1, inclusion "⊇" (`d = 3`): every member of the union of families I–III (each family at every site placement, times a unit phase; `IsQutritZeroFamilyMember`) is a normalized endpoint zero of rank at most two with `(C†C)² = C†C/2`, i.e. its nonzero singular values are `1/√2`. |
| `qutrit_endpoint_of_certificate` | Section 4.1, eqs. (12)–(15): an exact endpoint certificate implies T2.1a. The hypotheses are the certificate data: a Hermitian `Ph` (the carrier projector `Π_h`; only Hermiticity is assumed) fixing every feature `z_h = vec C ⊗ p ⊗ p` (Appendix B shows this for `Π_h`), with `C = X Y†` (Lean: `X * B`) and `p = bivecMat X` the bivector of the columns of `X` (Section 4.1), and positive semidefinite `Gh, Gm, Ga` with `Π_h Θ Π_h = G_h + Π_h Γ₃₄(G_m) Π_h + Π_h Γ₁₂₃₄(G_a) Π_h` (eq. (14); its support conditions `G_s = Π_s G_s Π_s` are not assumed). |
| `noisy_family_three_copy_of_endpoint` | Implication T2.1a ⇒ Corollary 6.2: with the qutrit seed, `noisyFamily J p` is three-copy nondistillable for `15/(d² + 15) < p < 1` (any `d`, `J` an isometry). |
| `projector_cut_identity` | Section 3.1, eq. (11) in two-factor form: for an orthonormal pair `u₁, u₂` on `L ⊗ R`, `∑_{r,s} e(u_r, u_s) = 2 Q(u₁u₁† + u₂u₂†)` (`biDefect`, `cutForm`). Here `e(u, v)` is defined by its expanded form `‖u‖²‖v‖² + |⟨v, u⟩|² - ‖P(u v†)‖²`; that it is a squared norm (Appendix A), and so `e ≥ 0`, is not part of this statement. |
| `cutForm_two_plane_projector` | Section 3.1, eq. (11), right-hand side: `2 Q(P) = 6 - ‖Tr_L P‖_F² - ‖Tr_R P‖_F²` for the projector `P = u₁u₁† + u₂u₂†` onto an orthonormal pair. |
| `two_plane_product` | Section 3.1: an orthonormal pair of fully product tensors whose sum is a product across the cuts `1\|23` and `2\|13` has `\|e₁⟩⟨e₁\| + \|e₂⟩⟨e₂\| = (P_E) ⊗ \|u⟩⟨u\| ⊗ \|v⟩⟨v\|` with the two-plane factor at site 1, 2 or 3. |
| `twoQubit_separable_iff_ppt` | Peres–Horodecki two-qubit criterion, quoted in the proof of Corollary 2.2: a two-qubit operator is separable (a finite nonnegative combination of products of positive semidefinite operators, the zero operator included) exactly when it and its partial transpose are positive semidefinite. |
| `appendixC_input1` | Appendix C, first analytic input: a rank-two qutrit matrix with `C² = κ C` satisfies `q(C) ≥ (s₁ - s₂)²/6` (`s₁`, `s₂` its two nonzero singular values; the bound is symmetric in them), and at a zero its range and corange are both thin at a common site. |
| `appendixC_input2` | Appendix C, second analytic input: a rank-two endpoint zero whose range contains a nonzero fully product vector has local range dimension at most two at every site. |
| `appendixC_input3` | Appendix C, third analytic input: a normalized endpoint zero of rank at most two with a thin local range lies in the union of families I–III. |

## How the Challenge definitions are kept faithful to the library

`Challenge.lean` copies the definitions of `ThreeCopyQutritWerner/Basic.lean`, verbatim and in order (from
`noncomputable section` to the end of the file), between `-- verbatim:` markers, and imports exactly the
Mathlib modules that `Basic.lean` sees (those of `ThreeCopyQutritWerner/Imports.lean`), so the copied
definitions elaborate to the same constants. `scripts/check-challenge-definitions.py` checks that the block
occurs character for character in `Basic.lean`, and a probe build compared Lean's structural hashes of the
statements, and of the project constants they use, in `Challenge.lean` and in `Solution.lean`
([verification/RECEIPTS.md](../verification/RECEIPTS.md), "Statement check").
