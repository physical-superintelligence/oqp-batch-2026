module

public import ThreeCopyQutritWerner.SingularUnitaryCompletion
public import ThreeCopyQutritWerner.SharpQutritExteriorLift
public import ThreeCopyQutritWerner.SharpQutritCoefficientAction

@[expose] public section


/-!
# Actual local unitary reduction of qutrit exterior coefficients

The actual singular decomposition of the full coefficient matrix gives a
nonnegative diagonal. Both exterior-coordinate unitaries have actual local
qutrit unitary lifts. Their physical tensor congruence therefore realizes
that diagonal form without a supplied normal-form or residual phase premise.
-/

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace ThreeCopyQutritWerner

/-- Every qutrit coefficient matrix is diagonalized by actual local exterior
actions. The right exterior action lifts the transpose of the right SVD unitary. -/
theorem sharpQutrit_coefficients_exists_diagonal_normal
    (K : Matrix (Fin 3) (Fin 3) ℂ) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ d : Fin 3 → ℝ,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧ (∀ i, 0 ≤ d i) ∧
        sharpQutritExteriorAction U * K * (sharpQutritExteriorAction V)ᵀ =
          Matrix.diagonal (fun i => (d i : ℂ)) := by
  obtain ⟨P, Q, d, hP, hQ, hd, hK⟩ := singularFamily_exists_unitary_diagonalization K
  have hPH : (Pᴴ)ᴴ * Pᴴ = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hP
  have hQT : (Qᵀ)ᴴ * Qᵀ = 1 := by
    simpa only [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      Matrix.transpose_mul, Matrix.transpose_one]
      using congrArg Matrix.transpose
        ((Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hQ)
  obtain ⟨U, hU, hEU⟩ := sharpQutritExteriorAction_exists_unitary_lift Pᴴ hPH
  obtain ⟨V, hV, hEV⟩ := sharpQutritExteriorAction_exists_unitary_lift Qᵀ hQT
  refine ⟨U, V, d, hU, hV, hd, ?_⟩
  rw [hEU, hEV, Matrix.transpose_transpose]
  exact hK

/-- The full physical double-antisymmetric matrix has a nonnegative diagonal
coefficient form under congruence by two actual local qutrit unitaries. -/
theorem sharpQutritAntiEncode_exists_diagonal_normal
    (K : Matrix (Fin 3) (Fin 3) ℂ) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ d : Fin 3 → ℝ,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧ (∀ i, 0 ≤ d i) ∧
        (U ⊗ₖ V) * sharpQutritAntiEncode K * (U ⊗ₖ V)ᵀ =
          sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) := by
  obtain ⟨U, V, d, hU, hV, hd, hK⟩ := sharpQutrit_coefficients_exists_diagonal_normal K
  refine ⟨U, V, d, hU, hV, hd, ?_⟩
  rw [sharpQutritAntiEncode_local_congruence, hK]

/-- The literal double-antisymmetric projection of every physical matrix
admits the same actual local unitary normal form, with coefficients recovered
from its original entries. No supplied encoder representation is required. -/
theorem sharpDoubleAnti_exists_qutrit_diagonal_normal
    (Z : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ d : Fin 3 → ℝ,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧ (∀ i, 0 ≤ d i) ∧
        (U ⊗ₖ V) * sharpDoubleAnti Z * (U ⊗ₖ V)ᵀ =
          sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) := by
  simpa only [sharpQutritAntiEncode_projected_coefficients] using
    sharpQutritAntiEncode_exists_diagonal_normal
      (sharpQutritAntiCoefficients (sharpDoubleAnti Z))

end ThreeCopyQutritWerner
