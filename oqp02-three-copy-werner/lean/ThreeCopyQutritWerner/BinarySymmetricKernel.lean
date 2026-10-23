module

public import ThreeCopyQutritWerner.BinaryZeros
public import ThreeCopyQutritWerner.CertificateReduction

@[expose] public section


/-!
# The actual binary endpoint form and its local symmetric kernel

The spin change of coordinates identifies the original endpoint form with
the squared norm of the actual threefold local symmetric projection. Both
directions of its zero-kernel characterization hold for every binary matrix,
without a rank or normalization premise.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- The literal one-site symmetric matrix is an orthogonal projection. -/
theorem psym_adjoint_mul_self : psymᴴ * psym = psym := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [psym, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.one_apply, swapOp, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Orthogonal projection is retained in the original three-copy register order. -/
theorem tripleCopy_psym_adjoint_mul_self :
    (tripleCopy psym)ᴴ * tripleCopy psym = tripleCopy psym := by
  rw [← tripleCopy_conjTranspose, ← tripleCopy_mul', psym_adjoint_mul_self]

/-- Exact original endpoint normalization under the binary spin transformation. -/
theorem endpointEnergy_spin_eq_expectation_psym
    (K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    (endpointEnergy (K * epsJ₃) : ℂ) = expectation (tripleCopy psym) (vec K) := by
  have h := expectation_partialTranspose_tripleCopy_werner 2 (1 / 2) (K * epsJ₃)
  rw [partialTranspose_tripleCopy, vec_mul_epsJ₃, expectation_mulVec,
    ← tripleCopy_conjTranspose, ← tripleCopy_mul', ← tripleCopy_mul',
    epsW_conj_partialTranspose_werner, tripleCopy_smul, expectation_smul_left] at h
  change (energy (1 / 2) (K * epsJ₃) : ℂ) = _
  norm_num at h
  exact h.symm

/-- The actual projection norm supplies the binary endpoint form exactly. -/
theorem endpointEnergy_spin_eq_projection_norm
    (K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    endpointEnergy (K * epsJ₃) = vecNormSq (tripleCopy psym *ᵥ vec K) := by
  apply Complex.ofReal_injective
  rw [endpointEnergy_spin_eq_expectation_psym, ← expectation_one_eq_vecNormSq,
    expectation_mulVec, Matrix.mul_one, tripleCopy_psym_adjoint_mul_self]

/-- Exact kernel equivalence for every original binary matrix, including zero. -/
theorem binary_endpoint_zero_iff_symmetric_kernel
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    endpointEnergy C = 0 ↔ tripleCopy psym *ᵥ vec (C * epsJ₃ᵀ) = 0 := by
  have hrec : C * epsJ₃ᵀ * epsJ₃ = C := by
    rw [Matrix.mul_assoc, epsJ₃_transpose_mul_self, Matrix.mul_one]
  have he := endpointEnergy_spin_eq_projection_norm (C * epsJ₃ᵀ)
  rw [hrec] at he
  rw [he]
  constructor
  · intro h
    funext i
    exact eq_zero_of_vecNormSq_eq_zero _ h i
  · intro h
    simp [h, vecNormSq]

end ThreeCopyQutritWerner
