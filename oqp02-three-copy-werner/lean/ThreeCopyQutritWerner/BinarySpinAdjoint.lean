module

public import ThreeCopyQutritWerner.BinaryZeros

@[expose] public section


/-! The actual adjoint of each binary spin form. The conjugated frame is
multiplied by the original spin matrix. The two-site form acquires a minus
phase; the three-site form does not. -/

noncomputable section
open scoped Matrix Kronecker
namespace ThreeCopyQutritWerner

theorem epsMat_conjTranspose_eq_neg : epsMatᴴ = -epsMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsMat]

theorem epsJ₂_transpose_conjTranspose : epsJ₂ᵀᴴ = epsJ₂ := by
  rw [epsJ₂_transpose, Matrix.conjTranspose_kronecker, epsMat_transpose_conjTranspose]
  rfl

theorem epsJ₃_transpose_conjTranspose : epsJ₃ᵀᴴ = epsJ₃ := by
  rw [epsJ₃_transpose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    epsMat_transpose_conjTranspose]
  rfl

theorem spin_conjugate_frame_isometry {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (hJ : Jᴴ * J = 1)
    (U : Matrix n (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    (J * Uᵀᴴ)ᴴ * (J * Uᵀᴴ) = 1 := by
  calc
    _ = Uᵀ * (Jᴴ * J) * Uᵀᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = 1 := by rw [hJ, Matrix.mul_one, transpose_mul_conjTranspose_transpose U hU]

theorem epsJ₂_conjugate_frame_isometry
    (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    (epsJ₂ * Uᵀᴴ)ᴴ * (epsJ₂ * Uᵀᴴ) = 1 := by
  apply spin_conjugate_frame_isometry _ _ U hU
  have h : epsJ₂ᴴ = epsJ₂ᵀ := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      (congrArg Matrix.conjTranspose epsJ₂_transpose_conjTranspose).symm
  rw [h, epsJ₂_transpose_mul_self]

theorem epsJ₃_conjugate_frame_isometry
    (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    (epsJ₃ * Uᵀᴴ)ᴴ * (epsJ₃ * Uᵀᴴ) = 1 := by
  apply spin_conjugate_frame_isometry _ _ U hU
  have h : epsJ₃ᴴ = epsJ₃ᵀ := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      (congrArg Matrix.conjTranspose epsJ₃_transpose_conjTranspose).symm
  rw [h, epsJ₃_transpose_mul_self]

private theorem spin_conjugate_frame_product {n : Type*} [Fintype n]
    (J : Matrix n n ℂ) (U : Matrix n (Fin 2) ℂ) :
    (J * Uᵀᴴ) * epsMat * (J * Uᵀᴴ)ᵀ * Jᵀ =
      J * (Uᵀᴴ * epsMat * Uᴴ) * (Jᵀ * Jᵀ) := by
  rw [Matrix.transpose_mul]
  change (J * Uᵀᴴ) * epsMat * (Uᴴ * Jᵀ) * Jᵀ = _
  simp only [Matrix.mul_assoc]

theorem binaryB₂_conjTranspose
    (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) :
    (binaryB₂ U)ᴴ = -binaryB₂ (epsJ₂ * Uᵀᴴ) := by
  have hb : binaryB₂ (epsJ₂ * Uᵀᴴ) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (epsJ₂ * (Uᵀᴴ * epsMat * Uᴴ)) := by
    rw [binaryB₂, epsJ₂_inv, spin_conjugate_frame_product,
      epsJ₂_transpose_mul_transpose, Matrix.mul_one]
  rw [hb, binaryB₂, epsJ₂_inv]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    epsJ₂_transpose_conjTranspose, epsMat_conjTranspose_eq_neg, Complex.star_def,
    Complex.conj_ofReal,
    Matrix.mul_neg, Matrix.neg_mul, smul_neg, Matrix.mul_assoc]

theorem binaryB₃_conjTranspose
    (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) :
    (binaryB₃ U)ᴴ = binaryB₃ (epsJ₃ * Uᵀᴴ) := by
  have hb : binaryB₃ (epsJ₃ * Uᵀᴴ) =
      -((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (epsJ₃ * (Uᵀᴴ * epsMat * Uᴴ))) := by
    rw [binaryB₃, epsJ₃_inv, spin_conjugate_frame_product, epsJ₃_transpose_mul_transpose]
    simp only [Matrix.mul_neg, Matrix.mul_one, smul_neg]
  rw [hb, binaryB₃, epsJ₃_inv]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    epsJ₃_transpose_conjTranspose, epsMat_conjTranspose_eq_neg, Complex.star_def,
    Complex.conj_ofReal, Matrix.mul_neg,
    Matrix.mul_one, Matrix.neg_mul, smul_neg, Matrix.mul_assoc]

end ThreeCopyQutritWerner
