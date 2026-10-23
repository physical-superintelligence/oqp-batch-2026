module

public import CausalNonpurifiability.Definitions.EffectCore

@[expose] public section


/-!
# `CausalNonpurifiability.Linear.Positive`

Positivity algebra for complex matrices on finite index types.  Everything is
stated for `Matrix ι ι ℂ`; the project abbreviation `Op ι := Matrix ι ι ℂ`
(owned by `Linear/Indices`) unfolds to it, so all lemmas apply to `Op ι` verbatim.

Contents:

* `Effect F := F.PosSemidef ∧ (1 - F).PosSemidef` — the effects `E_i`, `H_j` of
  `eq:operator-SOS`, `eq:DC`;
* Hermitian squares are PSD (`Aᴴ * A`, and `A * A`, `A ^ 2` for Hermitian `A`);
* `effect_sub_sq_psd : Effect F → (F - F * F).PosSemidef`, proved by the
  square-root-free congruence identity
  `F - F² = Fᴴ (1-F) F + (1-F)ᴴ F (1-F)` (`F` commutes with `1 - F`);
* trace pairing `0 ≤ trace (A * B)` for PSD `A B`: `B` is an additive combination of
  Hermitian squares `sᴴ s` (Loewner order, `StarOrderedRing.nonneg_iff`) and
  `Tr(A sᴴ s) = Tr(s A sᴴ) ≥ 0` by cyclicity (never "product of PSD is PSD");
* PSD closure under `ℕ`-multiples, nonnegative real scalars and sums;
* Kronecker products of PSD matrices, `Effect (E ⊗ₖ 1)`, `Effect (1 ⊗ₖ H)`;
* PSD / effect principal submatrices (compression
  `E_i(r,r') = E((i,r),(i,r'))`).

Manuscript anchors: `eq:positive-blocks`, `eq:Gram`, `eq:operator-SOS`, `eq:DC`.

Instance arguments are given per declaration (the current `Matrix.PosSemidef` needs no
`Fintype`; only products, traces, `1` and numerals do).
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace CausalNonpurifiability

variable {ι κ : Type}

/-! ### Effects -/


theorem Effect.posSemidef [DecidableEq ι] {F : Matrix ι ι ℂ} (h : Effect F) : F.PosSemidef := h.1

theorem Effect.one_sub_posSemidef [DecidableEq ι] {F : Matrix ι ι ℂ} (h : Effect F) :
    (1 - F).PosSemidef := h.2

theorem Effect.isHermitian [DecidableEq ι] {F : Matrix ι ι ℂ} (h : Effect F) : F.IsHermitian :=
  h.1.1

/-- `1 - F` is an effect when `F` is (`1 - (1 - F) = F`). -/
theorem Effect.one_sub [DecidableEq ι] {F : Matrix ι ι ℂ} (h : Effect F) : Effect (1 - F) :=
  ⟨h.2, by simpa using h.1⟩

theorem effect_zero [DecidableEq ι] : Effect (0 : Matrix ι ι ℂ) :=
  ⟨Matrix.PosSemidef.zero, by simpa using (Matrix.PosSemidef.one : (1 : Matrix ι ι ℂ).PosSemidef)⟩

theorem effect_one [DecidableEq ι] : Effect (1 : Matrix ι ι ℂ) :=
  ⟨Matrix.PosSemidef.one, by simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef)⟩

/-! ### Hermitian squares and congruences -/

/-- `Aᴴ A ≥ 0` for any rectangular `A` (Hermitian square, `eq:Gram`). -/
theorem conjTranspose_mul_self_psd [Fintype ι] [Fintype κ] (A : Matrix κ ι ℂ) :
    (Aᴴ * A).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self A

/-- `A Aᴴ ≥ 0` for any rectangular `A`. -/
theorem self_mul_conjTranspose_psd [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    (A * Aᴴ).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose A

/-- For Hermitian `A`, `A * A = Aᴴ A ≥ 0` ("every square is a Hermitian square",
`eq:operator-SOS`). -/
theorem hermitian_mul_self_psd [Fintype ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (A * A).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rwa [hA.eq] at h

/-- For Hermitian `A`, `A ^ 2 ≥ 0`. -/
theorem hermitian_sq_psd [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (A ^ 2).PosSemidef := by
  rw [sq]; exact hermitian_mul_self_psd hA

/-- Congruence `Bᴴ A B ≥ 0` for `A ≥ 0` (`eq:positive-blocks` style congruences). -/
theorem congruence_psd [Fintype ι] [Fintype κ] {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (B : Matrix ι κ ℂ) : (Bᴴ * A * B).PosSemidef :=
  hA.conjTranspose_mul_mul_same B

/-- Congruence `B A Bᴴ ≥ 0` for `A ≥ 0`. -/
theorem congruence_psd' [Fintype ι] [Fintype κ] {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (B : Matrix κ ι ℂ) : (B * A * Bᴴ).PosSemidef :=
  hA.mul_mul_conjTranspose_same B

/-- `F - F² ≥ 0` for an effect `F` (`eq:operator-SOS`: "`F - F² ≥ 0` for an effect `F`").
Square-root free: with `G = 1 - F` (which commutes with `F`),
`F - F² = F G = F G (F + G) = F G F + G F G = Fᴴ G F + Gᴴ F G`, a sum of two congruences of
PSD matrices by Hermitian matrices. -/
theorem effect_sub_sq_psd [Fintype ι] [DecidableEq ι] {F : Matrix ι ι ℂ} (hF : Effect F) :
    (F - F * F).PosSemidef := by
  have hH : F.IsHermitian := hF.isHermitian
  have key : F - F * F = Fᴴ * (1 - F) * F + (1 - F)ᴴ * F * (1 - F) := by
    rw [conjTranspose_sub, conjTranspose_one, hH.eq]
    noncomm_ring
  rw [key]
  exact (hF.2.conjTranspose_mul_mul_same F).add (hF.1.conjTranspose_mul_mul_same (1 - F))

/-- `F - F ^ 2 ≥ 0` for an effect `F` (power form of `effect_sub_sq_psd`). -/
theorem effect_sub_sq_psd' [Fintype ι] [DecidableEq ι] {F : Matrix ι ι ℂ} (hF : Effect F) :
    (F - F ^ 2).PosSemidef := by
  rw [sq]; exact effect_sub_sq_psd hF

/-! ### Trace pairing -/

/-- Trace pairing positivity `Tr(AB) ≥ 0` (in the `ComplexOrder`) for PSD `A`, `B`.
`B ≥ 0` in the Loewner order means `B` lies in the additive closure of the
Hermitian squares `sᴴ s` (`StarOrderedRing.nonneg_iff`); for each generator,
`Tr(A sᴴ s) = Tr(s A sᴴ) ≥ 0` by cyclicity and congruence, and the set
`{X | 0 ≤ Tr(A X)}` is an additive submonoid.  No "product of PSD is PSD" is used. -/
theorem trace_mul_nonneg [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  let S : AddSubmonoid (Matrix ι ι ℂ) :=
    { carrier := {X | 0 ≤ (A * X).trace}
      add_mem' := fun {X Y} (hX : 0 ≤ (A * X).trace) (hY : 0 ≤ (A * Y).trace) => by
        show 0 ≤ (A * (X + Y)).trace
        rw [mul_add, Matrix.trace_add]
        exact add_nonneg hX hY
      zero_mem' := by simp }
  have hgen : Set.range (fun s : Matrix ι ι ℂ => star s * s) ⊆ (S : Set (Matrix ι ι ℂ)) := by
    rintro _ ⟨s, rfl⟩
    show 0 ≤ (A * (star s * s)).trace
    rw [Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    exact (hA.mul_mul_conjTranspose_same s).trace_nonneg
  have hB' : B ∈ AddSubmonoid.closure (Set.range fun s : Matrix ι ι ℂ => star s * s) :=
    StarOrderedRing.nonneg_iff.mp (Matrix.nonneg_iff_posSemidef.mpr hB)
  have hmem : B ∈ S := (AddSubmonoid.closure_le.mpr hgen) hB'
  exact hmem

/-- Real part of the trace pairing of PSD matrices is nonnegative
(the Born-rule/`eq:DC` pairing `Tr[σ (37D₀₀ + …)] ≥ 0`). -/
theorem trace_mul_re_nonneg [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ ((A * B).trace).re :=
  (Complex.nonneg_iff.mp (trace_mul_nonneg hA hB)).1

/-- The trace pairing of PSD matrices is real. -/
theorem trace_mul_im_zero [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : ((A * B).trace).im = 0 :=
  ((Complex.nonneg_iff.mp (trace_mul_nonneg hA hB)).2).symm

/-- The trace of a PSD matrix has nonnegative real part. -/
theorem trace_re_nonneg [Fintype ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : 0 ≤ (A.trace).re :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

/-- The trace of a PSD matrix is real. -/
theorem trace_im_zero [Fintype ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : (A.trace).im = 0 :=
  ((Complex.nonneg_iff.mp hA.trace_nonneg).2).symm

/-! ### Nonnegative combinations -/

/-- `k • M ≥ 0` for `M ≥ 0`, `k : ℕ` (by induction, using only `PosSemidef.add`). -/
theorem posSemidef_nsmul {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (k : ℕ) : (k • M).PosSemidef := by
  induction k with
  | zero => simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef)
  | succ k ih =>
    rw [succ_nsmul]
    exact ih.add hM

/-- `(n : Matrix) * M ≥ 0` for `M ≥ 0`, `n : ℕ` (numeral coefficients of `eq:operator-SOS`). -/
theorem posSemidef_natCast_mul [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ} (hM : M.PosSemidef)
    (n : ℕ) : ((n : Matrix ι ι ℂ) * M).PosSemidef := by
  rw [← nsmul_eq_mul]; exact posSemidef_nsmul hM n

/-- Numeral-literal form of `posSemidef_natCast_mul`: `(OfNat.ofNat n : Matrix) * M ≥ 0`. -/
theorem posSemidef_ofNat_mul [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ} (hM : M.PosSemidef)
    (n : ℕ) [n.AtLeastTwo] : ((OfNat.ofNat n : Matrix ι ι ℂ) * M).PosSemidef :=
  posSemidef_natCast_mul hM n

/-- `c • M ≥ 0` for `M ≥ 0` and a nonnegative real scalar `c`. -/
theorem posSemidef_real_smul {M : Matrix ι ι ℂ} (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    (c • M).PosSemidef :=
  hM.smul hc

/-- `c • M ≥ 0` for `M ≥ 0` and `0 ≤ c` in the `ComplexOrder`. -/
theorem posSemidef_complex_smul {M : Matrix ι ι ℂ} (hM : M.PosSemidef) {c : ℂ} (hc : 0 ≤ c) :
    (c • M).PosSemidef :=
  hM.smul hc

/-- Nonnegative real combinations of PSD matrices are PSD (`eq:Gram`, `∑ cᵢ vᵢ vᵢᵀ` with `cᵢ ≥ 0`). -/
theorem posSemidef_sum_smul {α : Type} (s : Finset α) (c : α → ℝ) (M : α → Matrix ι ι ℂ)
    (hc : ∀ a ∈ s, 0 ≤ c a) (hM : ∀ a ∈ s, (M a).PosSemidef) :
    (∑ a ∈ s, c a • M a).PosSemidef := by
  refine Finset.sum_induction _ (fun X : Matrix ι ι ℂ => X.PosSemidef)
    (fun _ _ hX hY => hX.add hY) Matrix.PosSemidef.zero ?_
  intro a ha
  exact posSemidef_real_smul (hM a ha) (hc a ha)

/-- Dividing by two: `2 * S ≥ 0 → S ≥ 0` (clears the denominator of `eq:operator-SOS`). -/
theorem posSemidef_of_two_mul [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℂ}
    (h : (2 * S).PosSemidef) : S.PosSemidef := by
  have hS : S = (1 / 2 : ℝ) • (2 * S) := by
    ext i j
    simp only [two_mul, Matrix.smul_apply, Matrix.add_apply, Complex.real_smul]
    push_cast
    ring
  rw [hS]
  exact posSemidef_real_smul h (by norm_num)

/-! ### Hermitian closure under the ring operations used in the SOS -/

theorem isHermitian_nsmul {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (k : ℕ) :
    (k • A).IsHermitian := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul]
    exact ih.add hA

theorem isHermitian_natCast_mul [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (n : ℕ) : ((n : Matrix ι ι ℂ) * A).IsHermitian := by
  rw [← nsmul_eq_mul]; exact isHermitian_nsmul hA n

/-- `(OfNat.ofNat n : Matrix) * A` is Hermitian for Hermitian `A` (numeral coefficients in the
Hermitian squares `L`, `M` of `eq:operator-SOS`). -/
theorem isHermitian_ofNat_mul [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (n : ℕ) [n.AtLeastTwo] : ((OfNat.ofNat n : Matrix ι ι ℂ) * A).IsHermitian :=
  isHermitian_natCast_mul hA n

/-! ### Kronecker products -/

/-- Kronecker product of PSD matrices is PSD (`E_i ⊗ 1`, `1 ⊗ H_j` extensions of
`eq:operator-SOS`). -/
theorem posSemidef_kronecker [Fintype ι] [Fintype κ] {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊗ₖ B).PosSemidef :=
  hA.kronecker hB

theorem sub_kronecker' (A B : Matrix ι ι ℂ) (C : Matrix κ κ ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [sub_mul]

theorem kronecker_sub' (A : Matrix ι ι ℂ) (B C : Matrix κ κ ℂ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [mul_sub]

/-- Extending an effect by the identity on a second factor gives an effect
(as in `eq:DC`, where `E ⊗ I` stands for `E ⊗ I_{B_I R_B}`). -/
theorem effect_kronecker_one [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {E : Matrix ι ι ℂ} (hE : Effect E) : Effect (E ⊗ₖ (1 : Matrix κ κ ℂ)) := by
  refine ⟨posSemidef_kronecker hE.1 Matrix.PosSemidef.one, ?_⟩
  have h1 : (1 : Matrix (ι × κ) (ι × κ) ℂ) - E ⊗ₖ (1 : Matrix κ κ ℂ)
      = (1 - E) ⊗ₖ (1 : Matrix κ κ ℂ) := by
    rw [sub_kronecker', Matrix.one_kronecker_one]
  rw [h1]
  exact posSemidef_kronecker hE.2 Matrix.PosSemidef.one

/-- Extending an effect by the identity on a first factor gives an effect. -/
theorem effect_one_kronecker [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {H : Matrix κ κ ℂ} (hH : Effect H) : Effect ((1 : Matrix ι ι ℂ) ⊗ₖ H) := by
  refine ⟨posSemidef_kronecker Matrix.PosSemidef.one hH.1, ?_⟩
  have h1 : (1 : Matrix (ι × κ) (ι × κ) ℂ) - (1 : Matrix ι ι ℂ) ⊗ₖ H
      = (1 : Matrix ι ι ℂ) ⊗ₖ (1 - H) := by
    rw [kronecker_sub', Matrix.one_kronecker_one]
  rw [h1]
  exact posSemidef_kronecker Matrix.PosSemidef.one hH.2

/-! ### Principal submatrices -/

/-- PSD principal submatrix (compression `E_i(r,r') = E((i,r),(i,r'))`). -/
theorem posSemidef_submatrix {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (e : κ → ι) :
    (A.submatrix e e).PosSemidef :=
  hA.submatrix e

/-- Principal submatrix of an effect along an injective index map is an effect
("These are effects on `R_A` and on `R_B`", for the compressions `⟨i| E |i⟩`). -/
theorem effect_submatrix [DecidableEq ι] [DecidableEq κ] {E : Matrix ι ι ℂ} (hE : Effect E)
    {e : κ → ι} (he : Function.Injective e) : Effect (E.submatrix e e) := by
  refine ⟨posSemidef_submatrix hE.1 e, ?_⟩
  have h1 : (1 : Matrix κ κ ℂ) - E.submatrix e e = (1 - E).submatrix e e := by
    ext i j
    simp [Matrix.one_apply, he.eq_iff]
  rw [h1]
  exact posSemidef_submatrix hE.2 e

end CausalNonpurifiability
