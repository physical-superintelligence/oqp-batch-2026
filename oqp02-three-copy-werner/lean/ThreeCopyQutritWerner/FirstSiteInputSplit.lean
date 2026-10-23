module

public import ThreeCopyQutritWerner.FirstSiteBlocks
public import ThreeCopyQutritWerner.AppendixCInputs

@[expose] public section


/-!
# Splitting an input coordinate opposite a missing output coordinate

For a matrix with a missing first-site output coordinate k, its input-k
part and input-complement part have additive endpoint energies. The input-k
part has zero first partial trace and obeys the proved two-site inequality
block by block. Inheriting zeros for both parts uses the open original
endpoint inequality explicitly; no common input/output plane is assumed.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

variable {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a]

/-- Keep exactly one original first-site input coordinate. -/
def firstSiteInputKeep (C : Matrix (a × d) (a × d) ℂ) (k : a) :
    Matrix (a × d) (a × d) ℂ := fun p q => if q.1 = k then C p q else 0

/-- Keep its original input-coordinate complement. -/
def firstSiteInputDrop (C : Matrix (a × d) (a × d) ℂ) (k : a) :
    Matrix (a × d) (a × d) ℂ := fun p q => if q.1 = k then 0 else C p q

theorem firstSiteInputKeep_add_drop (C : Matrix (a × d) (a × d) ℂ) (k : a) :
    firstSiteInputKeep C k + firstSiteInputDrop C k = C := by
  ext p q
  by_cases h : q.1 = k <;> simp [firstSiteInputKeep, firstSiteInputDrop, h]

/-- The restrictions are actual right projections of the original matrix. -/
theorem firstSiteInputSplit_rank_le (C : Matrix (a × d) (a × d) ℂ) (k : a) :
    (firstSiteInputKeep C k).rank ≤ C.rank ∧
      (firstSiteInputDrop C k).rank ≤ C.rank := by
  classical
  have hk : firstSiteInputKeep C k =
      C * Matrix.diagonal (fun q : a × d => if q.1 = k then 1 else 0) := by
    ext p q
    by_cases h : q.1 = k <;> simp [firstSiteInputKeep, Matrix.mul_diagonal, h]
  have hd : firstSiteInputDrop C k =
      C * Matrix.diagonal (fun q : a × d => if q.1 = k then 0 else 1) := by
    ext p q
    by_cases h : q.1 = k <;> simp [firstSiteInputDrop, Matrix.mul_diagonal, h]
  rw [hk, hd]
  exact ⟨Matrix.rank_mul_le_left _ _, Matrix.rank_mul_le_left _ _⟩

theorem firstSiteBlock_inputKeep (C : Matrix (a × d) (a × d) ℂ) (k i j : a) :
    firstSiteBlock (firstSiteInputKeep C k) i j =
      if j = k then firstSiteBlock C i j else 0 := by
  ext r s
  by_cases h : j = k <;> simp [firstSiteBlock, firstSiteInputKeep, h]

theorem firstSiteBlock_inputDrop (C : Matrix (a × d) (a × d) ℂ) (k i j : a) :
    firstSiteBlock (firstSiteInputDrop C k) i j =
      if j = k then 0 else firstSiteBlock C i j := by
  ext r s
  by_cases h : j = k <;> simp [firstSiteBlock, firstSiteInputDrop, h]

variable {b c : Type*} [Fintype b] [Fintype c]

/-- No normalization factor is introduced by the coordinate restriction. -/
theorem firstSiteInputKeep_ptrace₁
    (C : Matrix (a × b × c) (a × b × c) ℂ) (k : a) :
    ptrace₁ (firstSiteInputKeep C k) = firstSiteBlock C k k := by
  ext r s
  simp [ptrace₁, firstSiteInputKeep, firstSiteBlock]

/-- A genuinely missing output row removes the first partial trace of the
input-k part, and preserves that trace in its input complement. -/
theorem firstSiteInputSplit_ptrace₁_of_missing_row
    (C : Matrix (a × b × c) (a × b × c) ℂ) (k : a)
    (hrow : ∀ r q, C (k, r) q = 0) :
    ptrace₁ (firstSiteInputKeep C k) = 0 ∧
      ptrace₁ (firstSiteInputDrop C k) = ptrace₁ C := by
  have hk : ptrace₁ (firstSiteInputKeep C k) = 0 := by
    rw [firstSiteInputKeep_ptrace₁]
    ext r s
    exact hrow r (k, s)
  refine ⟨hk, ?_⟩
  have he : ptrace₁ (firstSiteInputKeep C k) +
      ptrace₁ (firstSiteInputDrop C k) = ptrace₁ C := by
    ext r s
    simp only [ptrace₁, Matrix.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (congrFun (firstSiteInputKeep_add_drop C k) (i, r)) (i, s)
  simpa only [hk, zero_add] using he

private theorem firstSiteInputSplit_cutForm_zero :
    cutForm (0 : Matrix (b × c) (b × c) ℂ) = 0 := by
  simp [cutForm, frobSq, ptraceL, ptraceR, Matrix.trace]

/-- The physical endpoint energy splits exactly across these original input
coordinates whenever the opposite output coordinate is missing. -/
theorem endpointEnergy_firstSiteInputSplit
    (C : Matrix (a × b × c) (a × b × c) ℂ) (k : a)
    (hrow : ∀ r q, C (k, r) q = 0) :
    endpointEnergy C = endpointEnergy (firstSiteInputKeep C k) +
      endpointEnergy (firstSiteInputDrop C k) := by
  obtain ⟨hk, hd⟩ := firstSiteInputSplit_ptrace₁_of_missing_row C k hrow
  have hs : (∑ i, ∑ j, cutForm (firstSiteBlock (firstSiteInputKeep C k) i j)) +
      (∑ i, ∑ j, cutForm (firstSiteBlock (firstSiteInputDrop C k) i j)) =
        ∑ i, ∑ j, cutForm (firstSiteBlock C i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j = k <;>
      simp only [firstSiteBlock_inputKeep, firstSiteBlock_inputDrop, h,
        if_true, if_false, firstSiteInputSplit_cutForm_zero, zero_add, add_zero]
  simp only [endpointEnergy_eq_sum_firstSiteBlock_cutForm, hk, hd,
    firstSiteInputSplit_cutForm_zero]
  linarith

/-- The off-plane input part has nonnegative energy without assuming the
three-copy endpoint inequality. -/
theorem endpointEnergy_firstSiteInputKeep_nonneg [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2) (k : a)
    (hrow : ∀ r q, C (k, r) q = 0) :
    0 ≤ endpointEnergy (firstSiteInputKeep C k) := by
  rw [endpointEnergy_eq_sum_firstSiteBlock_cutForm,
    (firstSiteInputSplit_ptrace₁_of_missing_row C k hrow).1,
    firstSiteInputSplit_cutForm_zero, zero_div, sub_zero]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact firstSiteBlock_cutForm_nonneg _
    ((firstSiteInputSplit_rank_le C k).1.trans hC) i j

/-- The off-plane energy is exactly the sum of the original two-site block
energies, with no rank premise. -/
theorem endpointEnergy_firstSiteInputKeep_eq_sum
    (C : Matrix (a × b × c) (a × b × c) ℂ) (k : a)
    (hrow : ∀ r q, C (k, r) q = 0) :
    endpointEnergy (firstSiteInputKeep C k) =
      ∑ i, cutForm (firstSiteBlock C i k) := by
  rw [endpointEnergy_eq_sum_firstSiteBlock_cutForm,
    (firstSiteInputSplit_ptrace₁_of_missing_row C k hrow).1,
    firstSiteInputSplit_cutForm_zero, zero_div, sub_zero]
  simp [firstSiteBlock_inputKeep, apply_ite, firstSiteInputSplit_cutForm_zero]

/-- REDUCTION: the original endpoint inequality makes both original input
restrictions zeros at a missing-output-row zero. -/
theorem endpointEnergy_firstSiteInputSplit_zero
    (hendpoint : QutritEndpointInequality)
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (k : Fin 3)
    (hrow : ∀ r q, C (k, r) q = 0) :
    endpointEnergy (firstSiteInputKeep C k) = 0 ∧
      endpointEnergy (firstSiteInputDrop C k) = 0 := by
  have hk := endpointEnergy_firstSiteInputKeep_nonneg C hC k hrow
  have hd := hendpoint (firstSiteInputDrop C k)
    ((firstSiteInputSplit_rank_le C k).2.trans hC)
  have he := endpointEnergy_firstSiteInputSplit C k hrow
  constructor <;> linarith

/-- REDUCTION: every original off-plane two-site block is a cut-form zero.
Its rank bound was inherited from C, not imposed as an additional premise. -/
theorem firstSiteBlock_cutForm_zero_of_endpoint_zero
    (hendpoint : QutritEndpointInequality)
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (k : Fin 3)
    (hrow : ∀ r q, C (k, r) q = 0) (i : Fin 3) :
    cutForm (firstSiteBlock C i k) = 0 := by
  have hs := (endpointEnergy_firstSiteInputSplit_zero hendpoint C hC hz k hrow).1
  rw [endpointEnergy_firstSiteInputKeep_eq_sum C k hrow] at hs
  exact congrFun ((Fintype.sum_eq_zero_iff_of_nonneg
    (fun j => firstSiteBlock_cutForm_nonneg C hC j k)).mp hs) i

end ThreeCopyQutritWerner
