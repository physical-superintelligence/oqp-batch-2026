module

public import CausalNonpurifiability.Definitions.LVEquations
public import CausalNonpurifiability.Definitions.Instruments
public import CausalNonpurifiability.Linear.OpNorm

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.Channels`

Lemma 2.3 of the manuscript ("Processes and channels", `lem:channels`).

A *channel* of a party is represented by its operator `Mt` on input ⊗ output with
`Mt.PosSemidef` and `ptraceOut Mt = 1` (`eq:choi`).

* `LVEquations W` — the three homogeneous equations `eq:LV-a,b,c` without Hermiticity;
  `genLV_iff_lvEquations : GenLV W ↔ W.IsHermitian ∧ LVEquations W`.
* `lvEquations_of_channel_normalization` — the converse direction of the lemma for an arbitrary
  operator `W`: if `Tr[W (M ⊗ N)] = c` for all pairs of channels, then `W` satisfies `eq:LV` and
  `Tr W / (|A_O| |B_O|) = c`.
* `valid_iff_channel_normalization` — first statement of the lemma: a positive `W` is a process
  iff `Tr[W (M ⊗ N)] = 1` (`eq:normalisation`) for all pairs of channels.
* `Valid.extended` — second statement: `W ⊗ σ` is a process for the enlarged inputs.

Proof of the converse (manuscript): the reference channels are `I/|A_O|`, `I/|B_O|`; for a
Hermitian `K` the deviation `L = K − R(K)` is Hermitian and output-traceless, and
`I/|A_O| + ε L` is a channel for a small `ε > 0` (operator-norm bound).  Subtracting instances
of the hypothesis kills the three cross terms for Hermitian deviations, hence (ℂ-linearity) for
all deviations.  Since `1 − R` is the projection onto the deviations and the replacement maps
are Hilbert–Schmidt self-adjoint, the three equations hold when paired with every product
`K_A ⊗ K_B`, and products of single-entry matrices separate operators.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Kronecker Matrix ComplexOrder

namespace CausalNonpurifiability

noncomputable section

/-! ### Single-entry matrices separate operators -/

/-- The single-entry matrix `E_{p,q}`. -/
def unitMat {ι : Type} [DecidableEq ι] (p q : ι) : Op ι :=
  fun i j => if i = p ∧ j = q then 1 else 0

theorem unitMat_apply {ι : Type} [DecidableEq ι] (p q i j : ι) :
    unitMat p q i j = if i = p ∧ j = q then 1 else 0 := rfl

theorem unitMat_kronecker {I J : Type} [DecidableEq I] [DecidableEq J] (p₁ q₁ : I) (p₂ q₂ : J) :
    unitMat p₁ q₁ ⊗ₖ unitMat p₂ q₂ = unitMat (p₁, p₂) (q₁, q₂) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.kroneckerMap_apply, unitMat_apply, Prod.mk.injEq]
  by_cases a : i₁ = p₁ <;> by_cases b : j₁ = q₁ <;> by_cases c : i₂ = p₂ <;>
    by_cases d : j₂ = q₂ <;> simp [a, b, c, d]

/-- `Tr(Z E_{v,u}) = Z_{u,v}`. -/
theorem trace_mul_unitMat {ι : Type} [Fintype ι] [DecidableEq ι] (Z : Op ι) (u v : ι) :
    (Z * unitMat v u).trace = Z u v := by
  have h1 : ∀ x : ι, x ≠ u → ∑ y, Z x y * (if y = v ∧ x = u then (1 : ℂ) else 0) = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg (fun hh : y = v ∧ x = u => hx hh.2), mul_zero]
  have h2 : ∀ y : ι, y ≠ v → Z u y * (if y = v ∧ u = u then (1 : ℂ) else 0) = 0 := by
    intro y hy
    rw [if_neg (fun hh : y = v ∧ u = u => hy hh.1), mul_zero]
  have hsum : ∑ x, ∑ y, Z x y * (if y = v ∧ x = u then (1 : ℂ) else 0) = Z u v := by
    rw [Fintype.sum_eq_single u h1, Fintype.sum_eq_single v h2]
    simp
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, unitMat_apply]
  exact hsum

/-- Products `K ⊗ L` separate operators on a product index: if `Tr[Z (K ⊗ L)] = 0` for all
`K`, `L`, then `Z = 0`. -/
theorem eq_zero_of_trace_mul_kronecker_eq_zero {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Z : Op (I × J))
    (h : ∀ (K : Op I) (L : Op J), (Z * (K ⊗ₖ L)).trace = 0) : Z = 0 := by
  ext ⟨u₁, u₂⟩ ⟨v₁, v₂⟩
  have key := h (unitMat v₁ u₁) (unitMat v₂ u₂)
  rw [unitMat_kronecker, trace_mul_unitMat] at key
  exact key

/-! ### Hermitian operators span -/

/-- A `ℂ`-linear functional vanishing on Hermitian matrices vanishes identically
(`K = (K + Kᴴ)/2 − (i/2) · i (K − Kᴴ)`). -/
theorem eq_zero_of_forall_hermitian {ι : Type} (f : Op ι → ℂ)
    (hadd : ∀ X Y : Op ι, f (X + Y) = f X + f Y)
    (hsmul : ∀ (a : ℂ) (X : Op ι), f (a • X) = a * f X)
    (hf : ∀ K : Op ι, K.IsHermitian → f K = 0) (K : Op ι) : f K = 0 := by
  have h1 : (K + Kᴴ).IsHermitian := by
    show (K + Kᴴ)ᴴ = K + Kᴴ
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    exact add_comm _ _
  have h2 : (Complex.I • (K - Kᴴ)).IsHermitian := by
    show (Complex.I • (K - Kᴴ))ᴴ = Complex.I • (K - Kᴴ)
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]
  have hK : (1 / 2 : ℂ) • (K + Kᴴ) + (-Complex.I / 2) • (Complex.I • (K - Kᴴ)) = K := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination ((Kᴴ i j - K i j) / 2) * Complex.I_mul_I
  have key : f ((1 / 2 : ℂ) • (K + Kᴴ) + (-Complex.I / 2) • (Complex.I • (K - Kᴴ))) = 0 := by
    rw [hadd, hsmul, hsmul, hf _ h1, hf _ h2, mul_zero, mul_zero, add_zero]
  rw [hK] at key
  exact key

/-! ### Channels near the reference channel -/

section Perturbation

variable {I Y : Type} [Fintype I] [Fintype Y] [DecidableEq I] [DecidableEq Y]

/-- The reference channel `I/|Y|` is positive. -/
theorem posSemidef_invCard_smul_one : (invCard Y • (1 : Op (I × Y))).PosSemidef :=
  (Matrix.PosSemidef.one : (1 : Op (I × Y)).PosSemidef).smul (invCard_nonneg Y)

/-- The reference channel `I/|Y|` is normalized. -/
theorem ptraceOut_invCard_smul_one [Nonempty Y] :
    ptraceOut (invCard Y • (1 : Op (I × Y))) = 1 := by
  rw [ptraceOut_smul, ptraceOut_one, smul_smul, invCard_mul_card, one_smul]

/-- Every Hermitian `K` gives a channel `I/|Y| + ε (K − R K)` for some nonzero `ε`
("every Hermitian element of the kernel has a positive multiple that arises from a channel"). -/
theorem exists_channel_perturbation [Nonempty Y] {K : Op (I × Y)} (hK : K.IsHermitian) :
    ∃ ε : ℂ, ε ≠ 0 ∧ (invCard Y • (1 : Op (I × Y)) + ε • (K - replaceLast K)).PosSemidef ∧
      ptraceOut (invCard Y • (1 : Op (I × Y)) + ε • (K - replaceLast K)) = 1 := by
  obtain ⟨L, hLdef⟩ : ∃ L : Op (I × Y), L = K - replaceLast K := ⟨_, rfl⟩
  have hL : L.IsHermitian := by
    rw [hLdef]
    exact hK.sub (replaceLast_isHermitian hK)
  have hL0 : ptraceOut L = 0 := by
    rw [hLdef, ptraceOut_sub, ptraceOut_replaceLast, sub_self]
  obtain ⟨r, hr, hle⟩ : ∃ r : ℝ, 0 < r ∧ opNorm L ≤ r :=
    ⟨opNorm L + 1, by linarith [opNorm_nonneg L], by linarith⟩
  have hpsd : ((r : ℂ) • (1 : Op (I × Y)) + L).PosSemidef :=
    (psd_bounds_of_opNorm_le hL hr.le hle).1
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℂ, 0 ≤ s ∧ s * (r : ℂ) = 1 :=
    ⟨((r⁻¹ : ℝ) : ℂ), Complex.zero_le_real.mpr (inv_nonneg.mpr hr.le), by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one]⟩
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hs
    exact zero_ne_one hs
  refine ⟨invCard Y * s, mul_ne_zero (invCard_ne_zero Y) hsne, ?_, ?_⟩
  · have e : invCard Y • (1 : Op (I × Y)) + (invCard Y * s) • (K - replaceLast K)
        = invCard Y • (s • ((r : ℂ) • (1 : Op (I × Y)) + L)) := by
      rw [← hLdef]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination (-(invCard Y * (1 : Op (I × Y)) i j)) * hs
    rw [e]
    exact (hpsd.smul hs0).smul (invCard_nonneg Y)
  · rw [ptraceOut_add, ptraceOut_invCard_smul_one, ptraceOut_smul, ← hLdef, hL0, smul_zero,
      add_zero]

end Perturbation

section Generic
variable {A O B T : Type} [Fintype A] [Fintype O] [Fintype B] [Fintype T]
  [DecidableEq A] [DecidableEq O] [DecidableEq B] [DecidableEq T]

theorem genLV_iff_lvEquations (W : Op (LabIdx A O B T)) :
    GenLV W ↔ W.IsHermitian ∧ LVEquations W :=
  Iff.rfl

/-! ### Bilinearity of the pairing `(M, N) ↦ Tr[W (M ⊗ N)]` -/

theorem pair_add_left (W : Op (LabIdx A O B T)) (M M' : Op (A × O)) (N : Op (B × T)) :
    (W * ((M + M') ⊗ₖ N)).trace = (W * (M ⊗ₖ N)).trace + (W * (M' ⊗ₖ N)).trace := by
  rw [Matrix.add_kronecker, mul_add, Matrix.trace_add]

theorem pair_add_right (W : Op (LabIdx A O B T)) (M : Op (A × O)) (N N' : Op (B × T)) :
    (W * (M ⊗ₖ (N + N'))).trace = (W * (M ⊗ₖ N)).trace + (W * (M ⊗ₖ N')).trace := by
  rw [Matrix.kronecker_add, mul_add, Matrix.trace_add]

theorem pair_sub_left (W : Op (LabIdx A O B T)) (M M' : Op (A × O)) (N : Op (B × T)) :
    (W * ((M - M') ⊗ₖ N)).trace = (W * (M ⊗ₖ N)).trace - (W * (M' ⊗ₖ N)).trace := by
  rw [sub_kronecker', mul_sub, Matrix.trace_sub]

theorem pair_sub_right (W : Op (LabIdx A O B T)) (M : Op (A × O)) (N N' : Op (B × T)) :
    (W * (M ⊗ₖ (N - N'))).trace = (W * (M ⊗ₖ N)).trace - (W * (M ⊗ₖ N')).trace := by
  rw [kronecker_sub', mul_sub, Matrix.trace_sub]

theorem pair_smul_left (W : Op (LabIdx A O B T)) (a : ℂ) (M : Op (A × O)) (N : Op (B × T)) :
    (W * ((a • M) ⊗ₖ N)).trace = a * (W * (M ⊗ₖ N)).trace := by
  rw [Matrix.smul_kronecker, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

theorem pair_smul_right (W : Op (LabIdx A O B T)) (a : ℂ) (M : Op (A × O)) (N : Op (B × T)) :
    (W * (M ⊗ₖ (a • N))).trace = a * (W * (M ⊗ₖ N)).trace := by
  rw [Matrix.kronecker_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- The deviation `K ↦ K − R K` composed with the pairing is additive (Alice). -/
theorem dev_pair_add_left (W : Op (LabIdx A O B T)) (X Y : Op (A × O)) (N : Op (B × T)) :
    (W * ((X + Y - replaceLast (X + Y)) ⊗ₖ N)).trace =
      (W * ((X - replaceLast X) ⊗ₖ N)).trace + (W * ((Y - replaceLast Y) ⊗ₖ N)).trace := by
  have e : X + Y - replaceLast (X + Y) = (X - replaceLast X) + (Y - replaceLast Y) := by
    rw [replaceLast_add]
    abel
  rw [e, pair_add_left]

theorem dev_pair_smul_left (W : Op (LabIdx A O B T)) (a : ℂ) (X : Op (A × O)) (N : Op (B × T)) :
    (W * ((a • X - replaceLast (a • X)) ⊗ₖ N)).trace =
      a * (W * ((X - replaceLast X) ⊗ₖ N)).trace := by
  rw [replaceLast_smul, ← smul_sub, pair_smul_left]

/-- The deviation `K ↦ K − R K` composed with the pairing is additive (Bob). -/
theorem dev_pair_add_right (W : Op (LabIdx A O B T)) (M : Op (A × O)) (X Y : Op (B × T)) :
    (W * (M ⊗ₖ (X + Y - replaceLast (X + Y)))).trace =
      (W * (M ⊗ₖ (X - replaceLast X))).trace + (W * (M ⊗ₖ (Y - replaceLast Y))).trace := by
  have e : X + Y - replaceLast (X + Y) = (X - replaceLast X) + (Y - replaceLast Y) := by
    rw [replaceLast_add]
    abel
  rw [e, pair_add_right]

theorem dev_pair_smul_right (W : Op (LabIdx A O B T)) (a : ℂ) (M : Op (A × O)) (X : Op (B × T)) :
    (W * (M ⊗ₖ (a • X - replaceLast (a • X)))).trace =
      a * (W * (M ⊗ₖ (X - replaceLast X))).trace := by
  rw [replaceLast_smul, ← smul_sub, pair_smul_right]

/-! ### Replacement maps on Kronecker products -/

/-- `R_{B_I B_O}(M ⊗ N) = (Tr N / |B_I B_O|) · M ⊗ I`. -/
theorem R_BIBO_kronecker (M : Op (A × O)) (N : Op (B × T)) :
    R_BIBO (M ⊗ₖ N) = (N.trace * invCard (B × T)) • (M ⊗ₖ (1 : Op (B × T))) := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [R_BIBO_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.trace, Matrix.diag_apply]
  split_ifs with h
  · rw [h, Matrix.one_apply_eq, mul_one, ← Finset.mul_sum]
    ring
  · rw [Matrix.one_apply_ne h, mul_zero, mul_zero]

/-- `R_{A_I A_O}(M ⊗ N) = (Tr M / |A_I A_O|) · I ⊗ N`. -/
theorem R_AIAO_kronecker (M : Op (A × O)) (N : Op (B × T)) :
    R_AIAO (M ⊗ₖ N) = (M.trace * invCard (A × O)) • ((1 : Op (A × O)) ⊗ₖ N) := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [R_AIAO_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.trace, Matrix.diag_apply]
  split_ifs with h
  · rw [h, Matrix.one_apply_eq, one_mul, ← Finset.sum_mul]
    ring
  · rw [Matrix.one_apply_ne h, zero_mul, mul_zero]

theorem pair_R_AO (W : Op (LabIdx A O B T)) (M : Op (A × O)) (N : Op (B × T)) :
    (R_AO W * (M ⊗ₖ N)).trace = (W * (replaceLast M ⊗ₖ N)).trace := by
  rw [R_AO_pairing, R_AO_kronecker]

theorem pair_R_BO (W : Op (LabIdx A O B T)) (M : Op (A × O)) (N : Op (B × T)) :
    (R_BO W * (M ⊗ₖ N)).trace = (W * (M ⊗ₖ replaceLast N)).trace := by
  rw [R_BO_pairing, R_BO_kronecker]

theorem pair_R_BIBO (W : Op (LabIdx A O B T)) (M : Op (A × O)) (N : Op (B × T)) :
    (R_BIBO W * (M ⊗ₖ N)).trace =
      (N.trace * invCard (B × T)) * (W * (M ⊗ₖ (1 : Op (B × T)))).trace := by
  rw [R_BIBO_pairing, R_BIBO_kronecker, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

theorem pair_R_AIAO (W : Op (LabIdx A O B T)) (M : Op (A × O)) (N : Op (B × T)) :
    (R_AIAO W * (M ⊗ₖ N)).trace =
      (M.trace * invCard (A × O)) * (W * ((1 : Op (A × O)) ⊗ₖ N)).trace := by
  rw [R_AIAO_pairing, R_AIAO_kronecker, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-! ### Extracting the cross terms -/

/-- If the pairing takes the same value `c` on the four pairs built from `ιA`, `ιA + εA LA` and
`ιB`, `ιB + εB LB` (with `εA, εB ≠ 0`), then the three cross terms vanish. -/
theorem pairing_deviation_zero (W : Op (LabIdx A O B T)) (c : ℂ) {ιA LA : Op (A × O)}
    {ιB LB : Op (B × T)} {εA εB : ℂ} (hεA : εA ≠ 0) (hεB : εB ≠ 0)
    (h00 : (W * (ιA ⊗ₖ ιB)).trace = c)
    (h10 : (W * ((ιA + εA • LA) ⊗ₖ ιB)).trace = c)
    (h01 : (W * (ιA ⊗ₖ (ιB + εB • LB))).trace = c)
    (h11 : (W * ((ιA + εA • LA) ⊗ₖ (ιB + εB • LB))).trace = c) :
    (W * (LA ⊗ₖ ιB)).trace = 0 ∧ (W * (ιA ⊗ₖ LB)).trace = 0 ∧ (W * (LA ⊗ₖ LB)).trace = 0 := by
  simp only [pair_add_left, pair_smul_left, pair_add_right, pair_smul_right] at h10 h01 h11
  have e10 : εA * (W * (LA ⊗ₖ ιB)).trace = 0 := by linear_combination h10 - h00
  have e01 : εB * (W * (ιA ⊗ₖ LB)).trace = 0 := by linear_combination h01 - h00
  have p10 : (W * (LA ⊗ₖ ιB)).trace = 0 := (mul_eq_zero.mp e10).resolve_left hεA
  have p01 : (W * (ιA ⊗ₖ LB)).trace = 0 := (mul_eq_zero.mp e01).resolve_left hεB
  have e11 : εA * εB * (W * (LA ⊗ₖ LB)).trace = 0 := by
    linear_combination h11 - h00 - εB * p01 - εA * p10
  exact ⟨p10, p01, (mul_eq_zero.mp e11).resolve_left (mul_ne_zero hεA hεB)⟩

/-- Lemma 2.3, converse direction, for an arbitrary (not necessarily Hermitian) operator. -/
theorem lvEquations_of_channel_normalization [Nonempty O] [Nonempty T]
    (W : Op (LabIdx A O B T)) (c : ℂ)
    (h : ∀ (Mt : Op (A × O)) (Nt : Op (B × T)), Mt.PosSemidef → ptraceOut Mt = 1 →
      Nt.PosSemidef → ptraceOut Nt = 1 → (W * (Mt ⊗ₖ Nt)).trace = c) :
    LVEquations W ∧ invCard O * invCard T * W.trace = c := by
  -- the reference channels
  have hAp : (invCard O • (1 : Op (A × O))).PosSemidef := posSemidef_invCard_smul_one
  have hAt : ptraceOut (invCard O • (1 : Op (A × O))) = 1 := ptraceOut_invCard_smul_one
  have hBp : (invCard T • (1 : Op (B × T))).PosSemidef := posSemidef_invCard_smul_one
  have hBt : ptraceOut (invCard T • (1 : Op (B × T))) = 1 := ptraceOut_invCard_smul_one
  have h00 : (W * ((invCard O • (1 : Op (A × O))) ⊗ₖ (invCard T • (1 : Op (B × T))))).trace = c :=
    h _ _ hAp hAt hBp hBt
  have htr : invCard O * invCard T * W.trace = c := by
    have e : (W * ((invCard O • (1 : Op (A × O))) ⊗ₖ (invCard T • (1 : Op (B × T))))).trace
        = invCard O * invCard T * W.trace := by
      rw [pair_smul_left, pair_smul_right, Matrix.one_kronecker_one, Matrix.mul_one]
      ring
    rw [← e]
    exact h00
  -- cross terms for Hermitian deviations
  have key : ∀ (KA : Op (A × O)) (KB : Op (B × T)), KA.IsHermitian → KB.IsHermitian →
      (W * ((KA - replaceLast KA) ⊗ₖ (1 : Op (B × T)))).trace = 0 ∧
      (W * ((1 : Op (A × O)) ⊗ₖ (KB - replaceLast KB))).trace = 0 ∧
      (W * ((KA - replaceLast KA) ⊗ₖ (KB - replaceLast KB))).trace = 0 := by
    intro KA KB hKA hKB
    obtain ⟨εA, hεA, hpA, htA⟩ := exists_channel_perturbation hKA
    obtain ⟨εB, hεB, hpB, htB⟩ := exists_channel_perturbation hKB
    have h10 := h _ _ hpA htA hBp hBt
    have h01 := h _ _ hAp hAt hpB htB
    have h11 := h _ _ hpA htA hpB htB
    obtain ⟨p10, p01, p11⟩ := pairing_deviation_zero W c hεA hεB h00 h10 h01 h11
    rw [pair_smul_right] at p10
    rw [pair_smul_left] at p01
    exact ⟨(mul_eq_zero.mp p10).resolve_left (invCard_ne_zero T),
      (mul_eq_zero.mp p01).resolve_left (invCard_ne_zero O), p11⟩
  -- extension to all deviations by linearity
  have F1 : ∀ KA : Op (A × O),
      (W * ((KA - replaceLast KA) ⊗ₖ (1 : Op (B × T)))).trace = 0 := by
    intro KA
    exact eq_zero_of_forall_hermitian
      (fun K : Op (A × O) => (W * ((K - replaceLast K) ⊗ₖ (1 : Op (B × T)))).trace)
      (fun X Y => dev_pair_add_left W X Y 1) (fun a X => dev_pair_smul_left W a X 1)
      (fun K hK => (key K 0 hK Matrix.isHermitian_zero).1) KA
  have F2 : ∀ KB : Op (B × T),
      (W * ((1 : Op (A × O)) ⊗ₖ (KB - replaceLast KB))).trace = 0 := by
    intro KB
    exact eq_zero_of_forall_hermitian
      (fun K : Op (B × T) => (W * ((1 : Op (A × O)) ⊗ₖ (K - replaceLast K))).trace)
      (fun X Y => dev_pair_add_right W 1 X Y) (fun a X => dev_pair_smul_right W a 1 X)
      (fun K hK => (key 0 K Matrix.isHermitian_zero hK).2.1) KB
  have F3a : ∀ (KA : Op (A × O)) (KB : Op (B × T)), KB.IsHermitian →
      (W * ((KA - replaceLast KA) ⊗ₖ (KB - replaceLast KB))).trace = 0 := by
    intro KA KB hKB
    exact eq_zero_of_forall_hermitian
      (fun K : Op (A × O) => (W * ((K - replaceLast K) ⊗ₖ (KB - replaceLast KB))).trace)
      (fun X Y => dev_pair_add_left W X Y _) (fun a X => dev_pair_smul_left W a X _)
      (fun K hK => (key K KB hK hKB).2.2) KA
  have F3 : ∀ (KA : Op (A × O)) (KB : Op (B × T)),
      (W * ((KA - replaceLast KA) ⊗ₖ (KB - replaceLast KB))).trace = 0 := by
    intro KA KB
    exact eq_zero_of_forall_hermitian
      (fun K : Op (B × T) => (W * ((KA - replaceLast KA) ⊗ₖ (K - replaceLast K))).trace)
      (fun X Y => dev_pair_add_right W _ X Y) (fun a X => dev_pair_smul_right W a _ X)
      (fun K hK => F3a KA K hK) KB
  -- the three equations, tested against products
  have hZ1 : ∀ (KA : Op (A × O)) (KB : Op (B × T)),
      ((R_BIBO W - R_AO (R_BIBO W)) * (KA ⊗ₖ KB)).trace = 0 := by
    intro KA KB
    have e := F1 KA
    rw [pair_sub_left] at e
    simp only [sub_mul, Matrix.trace_sub, pair_R_AO, pair_R_BIBO]
    linear_combination (KB.trace * invCard (B × T)) * e
  have hZ2 : ∀ (KA : Op (A × O)) (KB : Op (B × T)),
      ((R_AIAO W - R_BO (R_AIAO W)) * (KA ⊗ₖ KB)).trace = 0 := by
    intro KA KB
    have e := F2 KB
    rw [pair_sub_right] at e
    simp only [sub_mul, Matrix.trace_sub, pair_R_BO, pair_R_AIAO]
    linear_combination (KA.trace * invCard (A × O)) * e
  have hZ3 : ∀ (KA : Op (A × O)) (KB : Op (B × T)),
      ((W - R_AO W - R_BO W + R_AO (R_BO W)) * (KA ⊗ₖ KB)).trace = 0 := by
    intro KA KB
    have e := F3 KA KB
    simp only [pair_sub_left, pair_sub_right] at e
    simp only [add_mul, sub_mul, Matrix.trace_add, Matrix.trace_sub, pair_R_AO, pair_R_BO]
    linear_combination e
  exact ⟨⟨eq_zero_of_trace_mul_kronecker_eq_zero _ hZ1,
    eq_zero_of_trace_mul_kronecker_eq_zero _ hZ2,
    eq_zero_of_trace_mul_kronecker_eq_zero _ hZ3⟩, htr⟩

end Generic

/-- Lemma 2.3, first statement. -/
theorem valid_iff_channel_normalization (D : Ports) {W : PMat D} (hW : W.PosSemidef) :
    Valid D W ↔ ∀ (Mt : Op (Fin D.m × Fin D.d)) (Nt : Op (Fin D.n × Fin D.e)),
      Mt.PosSemidef → ptraceOut Mt = 1 → Nt.PosSemidef → ptraceOut Nt = 1 →
      (W * (Mt ⊗ₖ Nt)).trace = 1 := by
  constructor
  · intro hV Mt Nt _ hM _ hN
    rw [GenLV.trace_mul_kronecker hV.1 hM hN, hV.2.2]
    exact invCard_fin_mul_card_mul D
  · intro h
    obtain ⟨hLV, htr⟩ := lvEquations_of_channel_normalization W 1 h
    have hc := invCard_fin_mul_card_mul D
    refine ⟨(genLV_iff_lvEquations W).mpr ⟨hW.1, hLV⟩, hW, ?_⟩
    linear_combination ((D.d * D.e : ℕ) : ℂ) * htr - W.trace * hc

/-- Lemma 2.3, second statement: `W ⊗ σ` is a process for the enlarged inputs. -/
theorem Valid.extended (D : Ports) {RA RB : Type} [Fintype RA] [Fintype RB] [DecidableEq RA]
    [DecidableEq RB] {W : PMat D} (hW : Valid D W) {σ : Op (RA × RB)} (hσ : Density σ) :
    GenLV (extended W σ) ∧ (extended W σ).PosSemidef ∧
      (extended W σ).trace = ((D.d * D.e : ℕ) : ℂ) := by
  refine ⟨GenLV.extended hW.1 hσ.1.1, posSemidef_extended hW.2.1 hσ.1, ?_⟩
  rw [trace_extended, hW.2.2, hσ.2, mul_one]

end

end CausalNonpurifiability
