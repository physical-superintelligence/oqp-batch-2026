module

public import ThreeCopyQutritWerner.TwoSiteFactorRanks

@[expose] public section


/-! Exact local matrix action on original rectangular two-site factors. -/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

variable {a b n : Type*} [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq a] [DecidableEq b] [DecidableEq n]

theorem twoSiteFactorFlatten_first_mul
    (U : Matrix a a ℂ) (X : Matrix (a × b) n ℂ) :
    twoSiteFactorFlatten ((U ⊗ₖ (1 : Matrix b b ℂ)) * X) = U * twoSiteFactorFlatten X := by
  ext i ⟨j, k⟩
  simp [twoSiteFactorFlatten, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul]

theorem twoSiteFactorFlatten_second_mul
    (V : Matrix b b ℂ) (X : Matrix (a × b) n ℂ) :
    twoSiteFactorFlatten (((1 : Matrix a a ℂ) ⊗ₖ V) * X) =
      twoSiteFactorFlatten X * (Vᵀ ⊗ₖ (1 : Matrix n n ℂ)) := by
  ext i ⟨j, k⟩
  simp [twoSiteFactorFlatten, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, mul_comm]

theorem twoSiteFactorFlatten_local_mul
    (U : Matrix a a ℂ) (V : Matrix b b ℂ) (X : Matrix (a × b) n ℂ) :
    twoSiteFactorFlatten ((U ⊗ₖ V) * X) =
      U * twoSiteFactorFlatten X * (Vᵀ ⊗ₖ (1 : Matrix n n ℂ)) := by
  have he : U ⊗ₖ V = (U ⊗ₖ (1 : Matrix b b ℂ)) * ((1 : Matrix a a ℂ) ⊗ₖ V) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [he, Matrix.mul_assoc, twoSiteFactorFlatten_first_mul,
    twoSiteFactorFlatten_second_mul, Matrix.mul_assoc]

theorem twoSiteFactorFlatten_local_mul_rank_le
    (U : Matrix a a ℂ) (V : Matrix b b ℂ) (X : Matrix (a × b) n ℂ) :
    (twoSiteFactorFlatten ((U ⊗ₖ V) * X)).rank ≤ (twoSiteFactorFlatten X).rank := by
  rw [twoSiteFactorFlatten_local_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem twoSiteFactorFlatten_local_unitary_rank
    (U : Matrix a a ℂ) (V : Matrix b b ℂ) (X : Matrix (a × b) n ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (twoSiteFactorFlatten ((U ⊗ₖ V) * X)).rank = (twoSiteFactorFlatten X).rank := by
  have he : (Uᴴ ⊗ₖ Vᴴ) * ((U ⊗ₖ V) * X) = X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, hU, hV,
      Matrix.one_kronecker_one, Matrix.one_mul]
  apply le_antisymm (twoSiteFactorFlatten_local_mul_rank_le U V X)
  have h := twoSiteFactorFlatten_local_mul_rank_le Uᴴ Vᴴ ((U ⊗ₖ V) * X)
  rwa [he] at h

end ThreeCopyQutritWerner
