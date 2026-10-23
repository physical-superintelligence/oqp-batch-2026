module

public import ThreeCopyQutritWerner.TwoSiteFactorLocalAction
public import ThreeCopyQutritWerner.ThinPencilFactors
public import ThreeCopyQutritWerner.TwoSiteJointFactorFlip

@[expose] public section


/-! Actual source-factor transport under retained-site changes of coordinates. -/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem factor_rank_left_isometry
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]
    (U : Matrix m n ℂ) (X : Matrix n p ℂ) (hU : Uᴴ * U = 1) :
    (U * X).rank = X.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  have he : Uᴴ * (U * X) = X := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have h := Matrix.rank_mul_le_right Uᴴ (U * X)
  rwa [he] at h

theorem firstSiteFactorBlock_remaining_mul
    {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a]
    (W : Matrix d d ℂ) (X : Matrix (a × d) (Fin 2) ℂ) (i : a) :
    firstSiteFactorBlock (((1 : Matrix a a ℂ) ⊗ₖ W) * X) i =
      W * firstSiteFactorBlock X i := by
  ext r j
  simp [firstSiteFactorBlock, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul]

theorem twoSiteFactorFlip_local_mul
    (U V : Matrix (Fin 3) (Fin 3) ℂ) (X : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ) :
    twoSiteFactorFlip ((U ⊗ₖ V) * X) = (V ⊗ₖ U) * twoSiteFactorFlip X := by
  ext ⟨i, j⟩ k
  simp only [twoSiteFactorFlip, Matrix.submatrix_apply, Equiv.prodComm_apply, id_eq,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Prod.swap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

end ThreeCopyQutritWerner
