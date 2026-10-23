module

public import ThreeCopyQutritWerner.TwoSiteJointFactorFlatten
public import ThreeCopyQutritWerner.TwoCutFixedSourceCoordinates
public import ThreeCopyQutritWerner.MatrixRangeFactor

@[expose] public section


/-! Actual local flattening ranks depend monotonically on column ranges. -/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem twoSiteFactorFlatten_mul_rank_le
    {a b m n : Type*} [Fintype a] [Fintype b] [Fintype m] [Fintype n]
    (X : Matrix (a × b) m ℂ) (R : Matrix m n ℂ) :
    (twoSiteFactorFlatten (X * R)).rank ≤ (twoSiteFactorFlatten X).rank := by
  classical
  have he : twoSiteFactorFlatten (X * R) =
      twoSiteFactorFlatten X * ((1 : Matrix b b ℂ) ⊗ₖ R) := by
    ext i ⟨j, s⟩
    simp [twoSiteFactorFlatten, Matrix.mul_apply, Matrix.kronecker_apply,
      Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul]
  rw [he]
  exact Matrix.rank_mul_le_left _ _

theorem twoSiteFactorFlatten_rank_le_of_range_le
    {a b m n : Type*} [Fintype a] [Fintype b] [Fintype m] [Fintype n]
    (X : Matrix (a × b) m ℂ) (Y : Matrix (a × b) n ℂ)
    (h : LinearMap.range X.mulVecLin ≤ LinearMap.range Y.mulVecLin) :
    (twoSiteFactorFlatten X).rank ≤ (twoSiteFactorFlatten Y).rank := by
  classical
  obtain ⟨R, hR⟩ := matrix_exists_right_factor_of_range_le X Y h
  rw [hR]
  exact twoSiteFactorFlatten_mul_rank_le Y R

theorem twoSiteFactorFlatten_rank_le_one_of_single_output
    {a b : Type*} [Fintype a] [Fintype b]
    (C : Matrix (a × b) (a × b) ℂ) (h : HasSingleFirstOutput C) :
    (twoSiteFactorFlatten C).rank ≤ 1 := by
  obtain ⟨k, x, _, hx⟩ := h
  have he : twoSiteFactorFlatten C =
      Matrix.vecMulVec x (fun q : b × (a × b) => C (k, q.1) q.2) := by
    ext i ⟨j, q⟩
    exact hx i j q
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

end ThreeCopyQutritWerner
