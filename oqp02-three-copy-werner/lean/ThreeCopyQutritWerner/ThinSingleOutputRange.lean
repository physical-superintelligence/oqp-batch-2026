module

public import ThreeCopyQutritWerner.ThinSingleOutput
public import ThreeCopyQutritWerner.TwoCutNonzeroRank
public import ThreeCopyQutritWerner.TwoCutBlockEmbedding
public import ThreeCopyQutritWerner.TwoCutSingleOutput

@[expose] public section


/-!
# Actual common ranges of nonzero single-output blocks

Two full-rank blocks in one original output row have the same range because
their adjoints have the rank of the full corresponding adjoint input column.
The single-output zero equations supply exact rank two for every nonzero block.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- Original rank-two blocks in one output row have the same actual range. -/
theorem firstSiteBlock_range_eq_of_rank_two
    {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a] [DecidableEq d]
    (C : Matrix (a × d) (a × d) ℂ) (hC : C.rank ≤ 2) (k i j : a)
    (hi : (firstSiteBlock C k i).rank = 2) (hj : (firstSiteBlock C k j).rank = 2) :
    LinearMap.range (firstSiteBlock C k i).mulVecLin =
      LinearMap.range (firstSiteBlock C k j).mulVecLin := by
  have hiH : (firstSiteBlock Cᴴ i k).rank = 2 := by
    rw [firstSiteBlock_conjTranspose, Matrix.rank_conjTranspose, hi]
  have hjH : (firstSiteBlock Cᴴ j k).rank = 2 := by
    rw [firstSiteBlock_conjTranspose, Matrix.rank_conjTranspose, hj]
  have hc : (firstSiteColumn Cᴴ k).rank = 2 := by
    have hlow := firstSiteBlock_rank_le_column Cᴴ i k
    have hupp := firstSiteColumn_rank_le Cᴴ k
    rw [hiH] at hlow
    rw [Matrix.rank_conjTranspose] at hupp
    omega
  have hei := firstSiteBlock_adjoint_range_eq_column Cᴴ i k (hiH.trans hc.symm)
  have hej := firstSiteBlock_adjoint_range_eq_column Cᴴ j k (hjH.trans hc.symm)
  simp only [firstSiteBlock_conjTranspose, Matrix.conjTranspose_conjTranspose] at hei hej
  exact hei.trans hej.symm

/-- The common source of all nonzero two-site cut-zero blocks is derived
from the original single-output endpoint zero and its global rank bound. -/
theorem single_output_nonzero_blocks_same_range
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (k : a)
    (hrow : ∀ l, l ≠ k → ∀ r q, C (l, r) q = 0) (i j : a)
    (hi : firstSiteBlock C k i ≠ 0) (hj : firstSiteBlock C k j ≠ 0) :
    (firstSiteBlock C k i).rank = 2 ∧ (firstSiteBlock C k j).rank = 2 ∧
      LinearMap.range (firstSiteBlock C k i).mulVecLin =
        LinearMap.range (firstSiteBlock C k j).mulVecLin := by
  have hq := firstSiteBlock_cutForm_zero_of_single_output_endpoint_zero C hC hz k hrow
  have hri := rank_two_of_nonzero_cutForm_zero _
    ((firstSiteBlock_rank_le C k i).trans hC) (hq i) hi
  have hrj := rank_two_of_nonzero_cutForm_zero _
    ((firstSiteBlock_rank_le C k j).trans hC) (hq j) hj
  exact ⟨hri, hrj, firstSiteBlock_range_eq_of_rank_two C hC k i j hri hrj⟩

end ThreeCopyQutritWerner
