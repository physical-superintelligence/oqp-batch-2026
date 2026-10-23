module

public import ThreeCopyQutritWerner
public import ThreeCopyQutritWerner.CertificateX2FinalProof

@[expose] public section


/-!
# Proofs of the statements in `Challenge.lean`

Each theorem below has exactly the statement of its counterpart in `Challenge.lean` and is proved
from the library `ThreeCopyQutritWerner`. `comparator.json` lists these theorems for Lean's
Comparator.

* `qutritEndpointInequality` (T2.1a) is `ThreeCopyQutritWerner.x2_qutritEndpointInequality`
  (`ThreeCopyQutritWerner/CertificateX2FinalProof.lean`), proved from an exact certificate: the
  manuscript's rational trial tuple with an exact rational correction on eight blocks that solves
  the coefficient equations exactly.
* `sharp_minimum`, `interior_minimizers`, `minimum_formula_unequal_dims`,
  `werner_three_three_copy_iff`, `werner_three_npt_not_three_copy` and `overlap_le_half` apply the
  implications `sharp_minimum_of_endpoint`, ..., `overlap_le_half_of_endpoint` to it.
* The other theorems are the corresponding library theorems.
-/

open scoped BigOperators ComplexOrder

namespace ThreeCopyQutritWerner.Endpoints

/-- Proposition 3.1, eq. (9). -/
theorem continuation_identity {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (α : ℝ) :
    energy α C - sharpCurve α * invN C =
      4 * α * (1 + α) / 3 * endpointEnergy C +
        α * (1 - 2 * α) * (2 / 3 - α) * formR C + 2 * α * (1 - 2 * α) * formS C :=
  energy_sub_sharpCurve_mul_invN C α

/-- Section 3, eq. (7): R ≥ 0 on rank at most two. -/
theorem formR_nonneg_rank_two {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (h : C.rank ≤ 2) : 0 ≤ formR C :=
  formR_nonneg_of_rank_le_two C h

/-- Section 3, eq. (8) and Appendix A: Q₁, Q₂, Q₃, S ≥ 0 on rank at most two. -/
theorem cutForms_nonneg_rank_two {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (h : C.rank ≤ 2) :
    0 ≤ cutForm₁ C ∧ 0 ≤ cutForm₂ C ∧ 0 ≤ cutForm₃ C ∧ 0 ≤ formS C :=
  ⟨cutForm₁_nonneg_of_rank_le_two C h, cutForm₂_nonneg_of_rank_le_two C h,
    cutForm₃_nonneg_of_rank_le_two C h, formS_nonneg_of_rank_le_two C h⟩

/-- eq. (6), the expectation identity. -/
theorem three_copy_expectation (d : ℕ) (α : ℝ)
    (C : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ) :
    expectation (partialTranspose (tripleCopy (werner d α))) (vec C) =
      (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) ^ 3 * ((energy α C : ℝ) : ℂ) :=
  expectation_partialTranspose_tripleCopy_werner d α C

/-- eq. (6): SR(vec C) = rank C. -/
theorem schmidtRank_vec {A B : Type*} [Fintype A] [Fintype B] (C : Matrix A B ℂ) (r : ℕ) :
    SchmidtRankLE r (vec C) ↔ C.rank ≤ r :=
  schmidtRankLE_vec_iff C r

/-- eq. (1): the Werner state. -/
theorem werner_state (d : ℕ) (hd : 2 ≤ d) (α : ℝ) (hm : -1 ≤ α) (h1 : α ≤ 1) :
    (werner d α).PosSemidef ∧ (werner d α).trace = 1 :=
  werner_isState d hd α hm h1

/-- Section 1: NPT exactly when α > 1/d. -/
theorem werner_npt_iff (d : ℕ) (hd : 2 ≤ d) (α : ℝ) (h1 : α ≤ 1) :
    IsNPT (werner d α) ↔ 1 / (d : ℝ) < α :=
  isNPT_werner_iff d hd α h1

/-- Section 1: one-copy distillable exactly when α > 1/2 (d = 3). -/
theorem werner_three_one_copy_iff {α : ℝ} (hm : -1 ≤ α) (h1 : α ≤ 1) :
    IsOneCopyFilterDistillable (werner 3 α) ↔ 1 / 2 < α :=
  isOneCopyFilterDistillable_werner_three_iff hm h1

/-- Corollary 2.2: distillable for 1/2 < α (d = 3). -/
theorem werner_three_three_copy_of_gt {α : ℝ} (h : 1 / 2 < α) (h1 : α ≤ 1) :
    IsThreeCopyFilterDistillable (werner 3 α) :=
  isThreeCopyFilterDistillable_werner_three h h1

/-- Corollary 2.2 proof: α ≤ 0 (d = 3). -/
theorem werner_three_not_three_copy_of_nonpos {α : ℝ} (h0 : α ≤ 0) :
    ¬ IsThreeCopyFilterDistillable (werner 3 α) :=
  not_isThreeCopyFilterDistillable_werner_three_of_nonpos h0

/-- Corollary 2.2 at `d = 3`, PPT region: for `α ≤ 1/3` three copies are not distillable (the state
has positive partial transpose there). -/
theorem werner_three_not_three_copy_of_le_third {α : ℝ} (h : α ≤ 1 / 3) :
    ¬ IsThreeCopyFilterDistillable (werner 3 α) :=
  not_isThreeCopyFilterDistillable_werner_three_of_le_third h

/-- Section 3: every matrix of the shape (5) attains the sharp curve. -/
theorem interior_shape_attains {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (h : IsInteriorMinimizerShape C) :
    C.rank ≤ 2 ∧ invN C = 1 ∧ ∀ α : ℝ, energy α C = sharpCurve α :=
  ⟨rank_le_two_of_isInteriorMinimizerShape C h,
    (energy_eq_sharpCurve_of_isInteriorMinimizerShape C h 0).1,
    fun α => (energy_eq_sharpCurve_of_isInteriorMinimizerShape C h α).2⟩

/-- eq. (21) (family I of Theorem 5.1, site 1 active): for every two-plane `E = span(f₁, f₂)`
(orthonormal pair) and unit `χ`, `η` on sites 2 and 3, `(P_E/√2) ⊗ |χ⟩⟨η|` is a normalized
endpoint zero of rank at most two, in any finite local dimensions. -/
theorem familyI_endpoint_zero_any_plane {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (f₁ f₂ : a → ℂ) (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) (h12 : braket f₁ f₂ = 0)
    (χ η : b × c → ℂ) (hχ : vecNormSq χ = 1) (hη : vecNormSq η = 1) :
    (tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)).rank ≤ 2 ∧
      invN (tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)) = 1 ∧
      endpointEnergy (tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)) = 0 :=
  familyI_endpoint_zero_general f₁ f₂ h1 h2 h12 χ η hχ hη

/-- Section 5.1: every nonzero endpoint zero has rank two. -/
theorem endpoint_zero_rank_two {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (h : C.rank ≤ 2) (h0 : endpointEnergy C = 0)
    (hC : C ≠ 0) : C.rank = 2 :=
  rank_eq_two_of_endpointEnergy_eq_zero C h h0 hC

/-- Corollary 2.2, separable operations, α ≤ 0 (d = 3). -/
theorem overlap_le_half_of_nonpos {α : ℝ} (h0 : α ≤ 0) {K : ℕ}
    (A : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (B : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (htp : ∀ u v : (Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3),
      ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
        (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) :
    maxEntOverlap (sepOutput A B (werner 3 α)) ≤ 1 / 2 :=
  werner_three_maxEntOverlap_le_of_nonpos h0 A B htp

/-- Corollary 2.2, separable operations, PPT region `α ≤ 1/3` (`d = 3`). -/
theorem overlap_le_half_of_le_third {α : ℝ} (h : α ≤ 1 / 3) {K : ℕ}
    (A : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (B : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (htp : ∀ u v : (Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3),
      ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
        (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) :
    maxEntOverlap (sepOutput A B (werner 3 α)) ≤ 1 / 2 :=
  werner_three_maxEntOverlap_le_of_le_third h A B htp

/-- The rank-two filter criterion: for Hermitian `ρ`, one (respectively three) copies are distillable by
local filters onto two qubits exactly when some vector of Schmidt rank at most two has negative expectation in
the partial transpose of `ρ` (respectively of `ρ^{⊗3}`). -/
theorem filter_iff_rank_two_detectable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (ρ : Matrix (m × n) (m × n) ℂ) (hρ : ρ.IsHermitian) :
    (IsOneCopyFilterDistillable ρ ↔ IsOneCopyRankTwoDetectable ρ) ∧
      (IsThreeCopyFilterDistillable ρ ↔ IsThreeCopyRankTwoDetectable ρ) :=
  ⟨isOneCopyFilterDistillable_iff ρ hρ, isThreeCopyFilterDistillable_iff ρ hρ⟩

/-- Theorem 2.1, eq. (4), attainment (`d = 3`): for every real `α` a normalized matrix of rank at
most two attains the sharp curve. -/
theorem sharp_curve_attained (α : ℝ) :
    ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = sharpCurve α :=
  exists_rank_le_two_energy_eq_sharpCurve α

/-- Implication T2.1a ⇒ T2.1b. -/
theorem sharp_minimum_of_endpoint : QutritEndpointInequality →
    ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 / 2 →
      (∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank ≤ 2 →
        sharpCurve α * invN C ≤ energy α C) ∧
      ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
        C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = sharpCurve α :=
  fun hq {α} h0 h1 =>
    ⟨fun C hC => sharpCurve_mul_invN_le_energy_of_endpointEnergy_nonneg C hC h0 h1 (hq C hC),
      exists_rank_le_two_energy_eq_sharpCurve α⟩

/-- Implication from T2.1a: Theorem 2.1, unequal dimensions, the case `2 ≤ dᵢ ≤ 3`. -/
theorem minimum_formula_of_card_of_endpoint {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] (ha2 : 2 ≤ Fintype.card a)
    (ha : Fintype.card a ≤ 3) (hb2 : 2 ≤ Fintype.card b) (hb : Fintype.card b ≤ 3)
    (hc2 : 2 ≤ Fintype.card c) (hc : Fintype.card c ≤ 3) : QutritEndpointInequality →
    ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 / 2 →
      (∀ C : Matrix (a × b × c) (a × b × c) ℂ, C.rank ≤ 2 →
        sharpCurve α * invN C ≤ energy α C) ∧
      ∃ C : Matrix (a × b × c) (a × b × c) ℂ,
        C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = sharpCurve α :=
  fun hq {_} h0 h1 => minimum_formula_of_card hq ha2 ha hb2 hb hc2 hc h0 h1

/-- Implication T2.1a ⇒ T2.1c. -/
theorem interior_minimizers_of_endpoint : QutritEndpointInequality →
    ∀ {α : ℝ}, 0 < α → α < 1 / 2 →
      ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank ≤ 2 → invN C = 1 →
        (∀ D : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, D.rank ≤ 2 →
          invN D = 1 → energy α C ≤ energy α D) →
        IsInteriorMinimizerShape C :=
  fun hq {_} h0 h1 C hC hN hmin => isInteriorMinimizerShape_of_isMin h0 h1 hq C hC hN hmin

/-- Implication T2.1a ⇒ C2.2a. -/
theorem werner_three_three_copy_iff_of_endpoint : QutritEndpointInequality →
    ∀ {α : ℝ}, α ≤ 1 → (IsThreeCopyFilterDistillable (werner 3 α) ↔ 1 / 2 < α) :=
  fun hq {_} h1 => isThreeCopyFilterDistillable_werner_three_iff_of_endpoint h1 hq

/-- Implication T2.1a ⇒ C2.2b. -/
theorem werner_three_npt_not_three_copy_of_endpoint : QutritEndpointInequality →
    ∀ {α : ℝ}, 1 / 3 < α → α ≤ 1 / 2 →
      IsNPT (werner 3 α) ∧ ¬ IsThreeCopyFilterDistillable (werner 3 α) :=
  fun hq {_} h0 h1 => werner_three_isNPT_and_not_distillable_of_endpoint h0 h1 hq

/-- Implication T2.1a ⇒ C2.2c (separable operations). -/
theorem overlap_le_half_of_endpoint : QutritEndpointInequality →
    ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 / 2 → ∀ {K : ℕ}
      (A : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
      (B : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ),
      (∀ u v : (Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3),
        ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
          (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) →
      maxEntOverlap (sepOutput A B (werner 3 α)) ≤ 1 / 2 :=
  fun hq {_} h0 h1 {_} A B htp => werner_three_maxEntOverlap_le_of_endpoint h0 h1 hq A B htp

/-- Section 3.1, eq. (10): for a Hermitian projector `P` of trace two with `P C = C`,
`R(C) = ‖C - (Tr C) P / 2‖_F²`. -/
theorem formR_eq_proj {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C P : Matrix (a × b × c) (a × b × c) ℂ) (hP : P.IsHermitian) (hPP : P * P = P)
    (htr : P.trace = 2) (hPC : P * C = C) :
    formR C = frobSq (C - (C.trace / 2) • P) :=
  formR_eq_frobSq_sub_proj C P hP hPP htr hPC

/-- Section 1 (`d = 3`): the partial trace over site 1 of a coefficient matrix of rank at most two
can have rank three. -/
theorem rank_raise_ptrace :
    ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ (ptrace₁ C).rank = 3 :=
  exists_rank_le_two_rank_ptrace₁_eq_three

/-- PPT region (`d = 3`, `α ≤ 1/3`): the partial transpose of three copies of the Werner state
is positive semidefinite, so no vector of any Schmidt rank detects three copies. -/
theorem three_copy_ppt_of_le_third {α : ℝ} (h : α ≤ 1 / 3) :
    (partialTranspose (tripleCopy (werner 3 α))).PosSemidef :=
  partialTranspose_tripleCopy_werner_three_posSemidef h

/-- The `d = 2` remark on Theorem 2.1: the qubit Werner state at `α = 1/2` is separable (for `α ≤ 1`
it is NPT exactly when `α > 1/2`, `werner_npt_iff` at `d = 2`). -/
theorem werner_two_half_separable : IsBipartiteSeparable (werner 2 (1 / 2)) :=
  werner_two_half_isSeparable

/-- Corollary 6.2: `noisyFamily J p` has full rank for `0 ≤ p < 1`. -/
theorem noisy_family_posDef {d : ℕ} (J : Matrix (Fin d) (Fin 3) ℂ) (hd : 0 < d) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1) : (noisyFamily J p).PosDef :=
  noisyFamily_posDef J hd hp0 hp1

/-- Corollary 6.2: for an isometry `J : ℂ³ → ℂᵈ`, `noisyFamily J p` is NPT for
`15/(d² + 15) < p ≤ 1`. (Its three-copy nondistillability follows from T2.1a:
`noisy_family_three_copy_of_endpoint`.) -/
theorem noisy_family_npt {d : ℕ} (J : Matrix (Fin d) (Fin 3) ℂ) (hJ : J.conjTranspose * J = 1)
    (hd : 0 < d) {p : ℝ} (hp : 15 / ((d : ℝ) ^ 2 + 15) < p) (hp1 : p ≤ 1) :
    IsNPT (noisyFamily J p) :=
  noisyFamily_isNPT J hJ hd hp hp1

/-- Implication from T2.1a: Theorem 2.1, eq. (4), as an attained minimum (`IsLeast`) over
normalized matrices of rank at most two. -/
theorem sharp_minimum_isLeast_of_endpoint : QutritEndpointInequality →
    ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 / 2 →
      IsLeast {x : ℝ | ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
        C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = x} (sharpCurve α) :=
  fun hq {α} h0 h1 => isLeast_energy_of_endpoint (α := α) hq h0 h1

/-- Theorem 5.1, inclusion "⊇" (`d = 3`): every member of the union of families I–III (each family
at every site placement, times a unit phase; `IsQutritZeroFamilyMember`) is a
normalized endpoint zero of rank at most two with `(C†C)² = C†C/2`, i.e. its nonzero singular values
are `1/√2`. -/
theorem zero_families_are_half_singular_zeros
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hC : IsQutritZeroFamilyMember C) :
    C.rank ≤ 2 ∧ invN C = 1 ∧ endpointEnergy C = 0 ∧
      C.conjTranspose * C * (C.conjTranspose * C) = (1 / 2 : ℂ) • (C.conjTranspose * C) :=
  isNormalizedHalfSingularZero_of_isQutritZeroFamilyMember hC

/-- Section 4.1, eqs. (12)–(15): an exact endpoint certificate implies T2.1a. The hypotheses are the
certificate data: a Hermitian `Ph` (the carrier projector `Π_h`; only Hermiticity is assumed)
fixing every feature `z_h = vec C ⊗ p ⊗ p` with `C = X B`, `p = bivecMat X` (Appendix B), and
positive semidefinite `Gh, Gm, Ga` with `Π_h (T ⊗ I) Π_h = G_h + Π_h Γ₃₄(G_m) Π_h + Π_h Γ₁₂₃₄(G_a) Π_h`
(eq. (14); its support conditions `G_s = Π_s G_s Π_s` are not assumed). -/
theorem qutrit_endpoint_of_certificate
    (Ph Gh Gm Ga : Matrix SixRegisters SixRegisters ℂ) (hPh : Ph.conjTranspose = Ph)
    (hcarrier : ∀ (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
      (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ),
      Ph.mulVec (featureH (X * B) (bivecMat X)) = featureH (X * B) (bivecMat X))
    (hgram : Ph * sixRegisterOperator * Ph =
      Gh + Ph * partialTranspose Gm * Ph + Ph * minorTranspose Ga * Ph)
    (hpsd : Gh.PosSemidef ∧ Gm.PosSemidef ∧ Ga.PosSemidef) :
    QutritEndpointInequality :=
  qutritEndpointInequality_of_certificate Ph Gh Gm Ga hPh hcarrier hgram hpsd

/-- Implication T2.1a ⇒ Corollary 6.2: with the qutrit seed, `noisyFamily J p` is three-copy
nondistillable for `15/(d² + 15) < p < 1` (any `d`, `J` an isometry). -/
theorem noisy_family_three_copy_of_endpoint : QutritEndpointInequality →
    ∀ (d : ℕ) (J : Matrix (Fin d) (Fin 3) ℂ), J.conjTranspose * J = 1 → ∀ p : ℝ,
      15 / ((d : ℝ) ^ 2 + 15) < p → p < 1 → ¬ IsThreeCopyFilterDistillable (noisyFamily J p) :=
  fun hq d J hJ p hp hp1 => noisyFamilyThreeCopyNondistillable_of_endpoint hq d J hJ p hp hp1

/-- Section 3.1, eq. (11) in two-factor form: for an orthonormal pair `u₁, u₂` on `L ⊗ R`,
`∑_{r,s} e(u_r, u_s) = 2 Q(u₁u₁† + u₂u₂†)` (`biDefect`, `cutForm`). Here `e(u, v)` is defined by its
expanded form `‖u‖²‖v‖² + |⟨v, u⟩|² - ‖P(u v†)‖²`; that it is a squared norm (Appendix A), and so
`e ≥ 0`, is not part of this statement. -/
theorem projector_cut_identity {L R : Type*} [Fintype L] [Fintype R] (u₁ u₂ : L × R → ℂ)
    (h1 : vecNormSq u₁ = 1) (h2 : vecNormSq u₂ = 1) (h12 : braket u₁ u₂ = 0) :
    biDefect u₁ u₁ + biDefect u₁ u₂ + biDefect u₂ u₁ + biDefect u₂ u₂ =
      2 * cutForm (ketBra u₁ u₁ + ketBra u₂ u₂) :=
  sum_biDefect_eq_two_mul_cutForm_proj u₁ u₂ h1 h2 h12

/-- Section 3.1, eq. (11), right-hand side: `2 Q(P) = 6 - ‖Tr_L P‖_F² - ‖Tr_R P‖_F²` for the
projector `P = u₁u₁† + u₂u₂†` onto an orthonormal pair. -/
theorem cutForm_two_plane_projector {L R : Type*} [Fintype L] [Fintype R] (u₁ u₂ : L × R → ℂ)
    (h1 : vecNormSq u₁ = 1) (h2 : vecNormSq u₂ = 1) (h12 : braket u₁ u₂ = 0) :
    2 * cutForm (ketBra u₁ u₁ + ketBra u₂ u₂) =
      6 - frobSq (ptraceL (ketBra u₁ u₁ + ketBra u₂ u₂)) -
        frobSq (ptraceR (ketBra u₁ u₁ + ketBra u₂ u₂)) :=
  two_mul_cutForm_proj u₁ u₂ h1 h2 h12

/-- Section 3.1: an orthonormal pair of fully product tensors whose sum is a product across the
cuts `1|23` and `2|13` has `|e₁⟩⟨e₁| + |e₂⟩⟨e₂| = (P_E) ⊗ |u⟩⟨u| ⊗ |v⟩⟨v|` with the two-plane
factor at site 1, 2 or 3. -/
theorem two_plane_product {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (a₁ b₁ : a → ℂ) (a₂ b₂ : b → ℂ) (a₃ b₃ : c → ℂ) (e₁ e₂ : a × b × c → ℂ)
    (he₁ : ∀ i j k, e₁ (i, j, k) = a₁ i * a₂ j * a₃ k)
    (he₂ : ∀ i j k, e₂ (i, j, k) = b₁ i * b₂ j * b₃ k)
    (hn₁ : vecNormSq e₁ = 1) (hn₂ : vecNormSq e₂ = 1) (ho : braket e₁ e₂ = 0)
    (hcut₁ : ∃ (α : a → ℂ) (β : b × c → ℂ), ∀ i j k, e₁ (i, j, k) + e₂ (i, j, k) = α i * β (j, k))
    (hcut₂ : ∃ (α : b → ℂ) (β : a × c → ℂ), ∀ i j k, e₁ (i, j, k) + e₂ (i, j, k) = α j * β (i, k)) :
    (∃ (f₁ f₂ : a → ℂ) (u : b → ℂ) (v : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        ketBra e₁ e₁ + ketBra e₂ e₂ = tensor₃ (ketBra f₁ f₁ + ketBra f₂ f₂) (ketBra u u) (ketBra v v)) ∨
    (∃ (u : a → ℂ) (f₁ f₂ : b → ℂ) (v : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        ketBra e₁ e₁ + ketBra e₂ e₂ = tensor₃ (ketBra u u) (ketBra f₁ f₁ + ketBra f₂ f₂) (ketBra v v)) ∨
    (∃ (u : a → ℂ) (v : b → ℂ) (f₁ f₂ : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        ketBra e₁ e₁ + ketBra e₂ e₂ = tensor₃ (ketBra u u) (ketBra v v) (ketBra f₁ f₁ + ketBra f₂ f₂)) :=
  two_plane_of_product a₁ b₁ a₂ b₂ a₃ b₃ e₁ e₂ he₁ he₂ hn₁ hn₂ ho hcut₁ hcut₂

/-- Peres–Horodecki two-qubit criterion, quoted in the proof of Corollary 2.2: a two-qubit operator
is separable (a finite nonnegative combination of products of positive semidefinite operators,
the zero operator included) exactly when it and its partial transpose are positive semidefinite. -/
theorem twoQubit_separable_iff_ppt
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    IsBipartiteSeparable ρ ↔ ρ.PosSemidef ∧ (partialTranspose ρ).PosSemidef :=
  ThreeCopyQutritWerner.twoQubit_separable_iff_ppt ρ

/- Appendix C analytical inputs. -/

open scoped Matrix

/-- Appendix C, first analytic input: a rank-two qutrit matrix with `C² = κ C` satisfies
`q(C) ≥ (s₁ - s₂)²/6` (`s₁`, `s₂` its two nonzero singular values; the bound is symmetric in them),
and at a zero its range and corange are both thin at a common site. -/
theorem appendixC_input1 :
  ∀ (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) (κ : ℂ), C.rank = 2 → C * C = κ • C →
    (frobSq C - 2 * Real.sqrt ((frobSq C ^ 2 - frobSq (Cᴴ * C)) / 2)) / 6 ≤ endpointEnergy C ∧
      (endpointEnergy C = 0 →
        ((ptrace₂₃ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₂₃ (Cᴴ * C)).rank ≤ 2) ∨
          ((ptrace₁₃ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₁₃ (Cᴴ * C)).rank ≤ 2) ∨
            ((ptrace₁₂ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₁₂ (Cᴴ * C)).rank ≤ 2)) := by
  exact appCInput1_proved

/-- Appendix C, second analytic input: a rank-two endpoint zero whose range contains a nonzero fully
product vector has local range dimension at most two at every site. -/
theorem appendixC_input2 :
  ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank = 2 → endpointEnergy C = 0 →
    (∃ x : (Fin 3 × Fin 3 × Fin 3) → ℂ, C *ᵥ x ≠ 0 ∧ (∃ (u v w : Fin 3 → ℂ), ∀ p : Fin 3 × Fin 3 × Fin 3,
        (C *ᵥ x) p = u p.1 * v p.2.1 * w p.2.2)) →
      (ptrace₂₃ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₁₃ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₁₂ (C * Cᴴ)).rank ≤ 2 := by
  exact appCInput2_product_ray

/-- Appendix C, third analytic input: a normalized endpoint zero of rank at most two with a thin
local range lies in the union of families I–III. -/
theorem appendixC_input3 :
  ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank ≤ 2 → invN C = 1 → endpointEnergy C = 0 →
    ((ptrace₂₃ (C * Cᴴ)).rank ≤ 2 ∨ (ptrace₁₃ (C * Cᴴ)).rank ≤ 2 ∨ (ptrace₁₂ (C * Cᴴ)).rank ≤ 2) → IsQutritZeroFamilyMember C := by
  exact appCInput3_proved

/-! ## T2.1a and the six claims that depend on it -/

/-- Theorem 2.1 of the manuscript at `d = 3`, `α = 1/2` (claim T2.1a), the qutrit endpoint
inequality: `q(C) ≥ 0` for every complex `27 × 27` matrix `C` of rank at most two, where
`q = endpointEnergy` is the three-copy form `q_{1/2}` (`QutritEndpointInequality`). -/
theorem qutritEndpointInequality : QutritEndpointInequality :=
  ThreeCopyQutritWerner.x2_qutritEndpointInequality

/-- Theorem 2.1, eq. (4), at `d = 3` (claim T2.1b): for `0 ≤ α ≤ 1/2`, `q_α(C) ≥ (1 - 2α)(1 - α)² ‖C‖_F²` for
every matrix of rank at most two, with equality for some normalized matrix of rank at most two. -/
theorem sharp_minimum {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) :
    (∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank ≤ 2 →
      sharpCurve α * invN C ≤ energy α C) ∧
    ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = sharpCurve α :=
  sharp_minimum_of_endpoint qutritEndpointInequality h0 h1

/-- Theorem 2.1, eq. (5), at `d = 3` (claim T2.1c): for `0 < α < 1/2`, every normalized minimizer of `q_α`
over rank at most two has the shape of eq. (5) up to a permutation of the sites. -/
theorem interior_minimizers {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2)
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hC : C.rank ≤ 2) (hN : invN C = 1)
    (hmin : ∀ D : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, D.rank ≤ 2 →
      invN D = 1 → energy α C ≤ energy α D) :
    IsInteriorMinimizerShape C :=
  interior_minimizers_of_endpoint qutritEndpointInequality h0 h1 C hC hN hmin

/-- Theorem 2.1, unequal dimensions, the case `2 ≤ dᵢ ≤ 3` (claim T2.1d): for `0 ≤ α ≤ 1/2`,
`q_α(C) ≥ (1 - 2α)(1 - α)² ‖C‖_F²` for every matrix of rank at most two on sites of dimensions
`2 ≤ dᵢ ≤ 3`, with equality for some normalized matrix of rank at most two. -/
theorem minimum_formula_unequal_dims {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] (ha2 : 2 ≤ Fintype.card a)
    (ha : Fintype.card a ≤ 3) (hb2 : 2 ≤ Fintype.card b) (hb : Fintype.card b ≤ 3)
    (hc2 : 2 ≤ Fintype.card c) (hc : Fintype.card c ≤ 3) :
    ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 / 2 →
      (∀ C : Matrix (a × b × c) (a × b × c) ℂ, C.rank ≤ 2 →
        sharpCurve α * invN C ≤ energy α C) ∧
      ∃ C : Matrix (a × b × c) (a × b × c) ℂ,
        C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = sharpCurve α :=
  minimum_formula_of_card_of_endpoint ha2 ha hb2 hb hc2 hc qutritEndpointInequality

/-- Corollary 2.2 at `d = 3` (claim C2.2a): for `α ≤ 1`, three copies of the qutrit Werner state are
distillable exactly when `α > 1/2`. -/
theorem werner_three_three_copy_iff {α : ℝ} (h1 : α ≤ 1) :
    IsThreeCopyFilterDistillable (werner 3 α) ↔ 1 / 2 < α :=
  werner_three_three_copy_iff_of_endpoint qutritEndpointInequality h1

/-- Corollary 2.2 at `d = 3` (claim C2.2b): for `1/3 < α ≤ 1/2` the qutrit Werner state is NPT and three
copies of it are not distillable. -/
theorem werner_three_npt_not_three_copy {α : ℝ} (h0 : 1 / 3 < α) (h1 : α ≤ 1 / 2) :
    IsNPT (werner 3 α) ∧ ¬ IsThreeCopyFilterDistillable (werner 3 α) :=
  werner_three_npt_not_three_copy_of_endpoint qutritEndpointInequality h0 h1

/-- Corollary 2.2, at `d = 3` (claim C2.2c): for `0 ≤ α ≤ 1/2`, every trace-preserving
separable operation from three copies of the qutrit Werner state to two qubits outputs an operator
whose overlap with the maximally entangled state is at most `1/2`. -/
theorem overlap_le_half {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) {K : ℕ}
    (A : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (B : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (htp : ∀ u v : (Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3),
      ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
        (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) :
    maxEntOverlap (sepOutput A B (werner 3 α)) ≤ 1 / 2 :=
  overlap_le_half_of_endpoint qutritEndpointInequality h0 h1 A B htp

end ThreeCopyQutritWerner.Endpoints
