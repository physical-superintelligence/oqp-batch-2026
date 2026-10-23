module

public import ThreeCopyQutritWerner.RankTwoProductRanges
public import ThreeCopyQutritWerner.TwoCutCommonCarrier
public import ThreeCopyQutritWerner.MatrixRangeFactor

@[expose] public section


/-!
# The actual source and corange factors share a constructed cut carrier

Full two-column rank identifies both original factor ranges with those of
the cut-zero product and its adjoint. The proved common binary carrier of
that product therefore contains both actual factors, with literal right
coefficient matrices constructed from range inclusion.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem cutForm_zero_full_factors_common_carrier
    (X Y : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ)
    (hX : X.rank = 2) (hY : Y.rank = 2) (hq : cutForm (X * Yᴴ) = 0) :
    ∃ (J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ)
      (R S : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ),
      J₁ᴴ * J₁ = 1 ∧ J₂ᴴ * J₂ = 1 ∧
        X = (J₁ ⊗ₖ J₂) * R ∧ Y = (J₁ ⊗ₖ J₂) * S := by
  obtain ⟨hr, hRX, hRY⟩ := full_two_column_product_rank_ranges X Y hX hY
  obtain ⟨J₁, J₂, K, hJ₁, hJ₂, he⟩ := cutForm_zero_exists_binary_carrier (X * Yᴴ) hr.le hq
  obtain ⟨R, hR⟩ := matrix_exists_right_factor_of_range_le X (X * Yᴴ) hRX.symm.le
  obtain ⟨S, hS⟩ := matrix_exists_right_factor_of_range_le Y ((X * Yᴴ)ᴴ) hRY.symm.le
  refine ⟨J₁, J₂, K * (J₁ ⊗ₖ J₂)ᴴ * R,
    Kᴴ * (J₁ ⊗ₖ J₂)ᴴ * S, hJ₁, hJ₂, ?_, ?_⟩
  · calc
      X = (X * Yᴴ) * R := hR
      _ = (J₁ ⊗ₖ J₂) * (K * (J₁ ⊗ₖ J₂)ᴴ * R) := by
        rw [he]
        simp only [Matrix.mul_assoc]
  · calc
      Y = (X * Yᴴ)ᴴ * S := hS
      _ = (J₁ ⊗ₖ J₂) * (Kᴴ * (J₁ ⊗ₖ J₂)ᴴ * S) := by
        rw [he]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

end ThreeCopyQutritWerner
