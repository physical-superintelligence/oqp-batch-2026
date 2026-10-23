module

public import ThreeCopyQutritWerner.SharpQutritExteriorAction
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section


/-!
# Full qutrit coefficient transport under actual local congruence

The two local exterior actions transport the complete nine-entry coefficient
matrix. The physical operation is literal congruence by `U ⊗ V`, with ordinary
transpose on the second side. No unitarity or normal-form premise is needed
for this polynomial identity.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Kronecker

namespace ThreeCopyQutritWerner

/-- The physical encoder is the exact sum of tensor products of the two
original cyclic wedge bases. -/
theorem sharpQutritAntiEncode_eq_sum (K : Matrix (Fin 3) (Fin 3) ℂ) :
    sharpQutritAntiEncode K =
      ∑ a, ∑ b, K a b • (sharpQutritWedgeBasis a ⊗ₖ sharpQutritWedgeBasis b) := by
  ext i j
  simp only [sharpQutritAntiEncode, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.kroneckerMap_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Matrix multiplication of the exterior coefficients agrees with the two
independent linear changes of the actual wedge basis. -/
theorem sharpQutritAntiEncode_coefficient_mul
    (P K Q : Matrix (Fin 3) (Fin 3) ℂ) :
    sharpQutritAntiEncode (P * K * Qᵀ) =
      ∑ a, ∑ b, K a b •
        ((∑ r, P r a • sharpQutritWedgeBasis r) ⊗ₖ
          (∑ s, Q s b • sharpQutritWedgeBasis s)) := by
  ext i j
  simp only [sharpQutritAntiEncode, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sum_swap_22]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem sharpQutrit_tensor_congruence
    (U V A B : Matrix (Fin 3) (Fin 3) ℂ) :
    (U ⊗ₖ V) * (A ⊗ₖ B) * (U ⊗ₖ V)ᵀ =
      (U * A * Uᵀ) ⊗ₖ (V * B * Vᵀ) := by
  rw [← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]

/-- Full coefficient congruence for the original physical double-antisymmetric
matrix. The transpose is essential: these are replica coefficient tensors. -/
theorem sharpQutritAntiEncode_local_congruence
    (U V K : Matrix (Fin 3) (Fin 3) ℂ) :
    (U ⊗ₖ V) * sharpQutritAntiEncode K * (U ⊗ₖ V)ᵀ =
      sharpQutritAntiEncode
        (sharpQutritExteriorAction U * K * (sharpQutritExteriorAction V)ᵀ) := by
  rw [sharpQutritAntiEncode_eq_sum]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp_rw [sharpQutrit_tensor_congruence, sharpQutritWedgeBasis_congruence]
  exact (sharpQutritAntiEncode_coefficient_mul
    (sharpQutritExteriorAction U) K (sharpQutritExteriorAction V)).symm

/-- Extracting the original cyclic entries after physical local congruence
gives precisely the transported exterior coefficient matrix. -/
theorem sharpQutritAntiCoefficients_local_congruence
    (U V K : Matrix (Fin 3) (Fin 3) ℂ) :
    sharpQutritAntiCoefficients
      ((U ⊗ₖ V) * sharpQutritAntiEncode K * (U ⊗ₖ V)ᵀ) =
      sharpQutritExteriorAction U * K * (sharpQutritExteriorAction V)ᵀ := by
  rw [sharpQutritAntiEncode_local_congruence, sharpQutritAntiCoefficients_encode]

end ThreeCopyQutritWerner
