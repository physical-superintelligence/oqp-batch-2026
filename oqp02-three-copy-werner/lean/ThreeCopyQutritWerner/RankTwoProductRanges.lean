module

public import ThreeCopyQutritWerner.ZeroRelations
public import ThreeCopyQutritWerner.OrthogonalProjectionRange

@[expose] public section


/-! Literal source and corange of products with actual full two-column factors. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem rank_mul_conjTranspose_eq_of_full_two_columns
    {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m (Fin 2) ℂ) (Y : Matrix n (Fin 2) ℂ) (hY : Y.rank = 2) :
    (X * Yᴴ).rank = X.rank := by
  have hYH : Yᴴ.rank = 2 := by rw [Matrix.rank_conjTranspose, hY]
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_eq_two Yᴴ hYH
  apply le_antisymm (Matrix.rank_mul_le_left X Yᴴ)
  calc
    X.rank = (X * Yᴴ * R).rank := by rw [Matrix.mul_assoc, hR, Matrix.mul_one]
    _ ≤ (X * Yᴴ).rank := Matrix.rank_mul_le_left _ _

/-- Both actual full-column-rank hypotheses identify the original product's
rank, source and corange. No range equality is an additional premise. -/
theorem full_two_column_product_rank_ranges
    {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m (Fin 2) ℂ) (Y : Matrix n (Fin 2) ℂ)
    (hX : X.rank = 2) (hY : Y.rank = 2) :
    (X * Yᴴ).rank = 2 ∧
      LinearMap.range (X * Yᴴ).mulVecLin = LinearMap.range X.mulVecLin ∧
      LinearMap.range ((X * Yᴴ)ᴴ).mulVecLin = LinearMap.range Y.mulVecLin := by
  have hr := rank_mul_conjTranspose_eq_of_full_two_columns X Y hY
  refine ⟨hr.trans hX, matrix_range_mul_eq_of_rank_eq X Yᴴ hr, ?_⟩
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  exact matrix_range_mul_eq_of_rank_eq Y Xᴴ
    (rank_mul_conjTranspose_eq_of_full_two_columns Y X hX)

end ThreeCopyQutritWerner
