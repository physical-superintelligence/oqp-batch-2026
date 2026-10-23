module

public import ThreeCopyQutritWerner.SharpQutritExteriorAction
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

@[expose] public section


/-!
# Lifting a unitary exterior action to an actual local qutrit unitary

The cyclic exterior action has degree two. A square root of the target
determinant corrects the phase of its entrywise conjugate exactly.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Scalar multiplication has degree two on the actual exterior coordinates. -/
theorem sharpQutritExteriorAction_smul (z : ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ) :
    sharpQutritExteriorAction (z • U) = z ^ 2 • sharpQutritExteriorAction U := by
  ext a b
  simp only [sharpQutritExteriorAction_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Entrywise complex conjugation preserves the literal unitary equation. -/
theorem sharpQutrit_conjugate_isometry (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hV : Vᴴ * V = 1) : ((Vᴴ)ᵀ)ᴴ * (Vᴴ)ᵀ = 1 := by
  simpa only [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.transpose_mul, Matrix.transpose_one]
    using congrArg Matrix.transpose hV

/-- The determinant square root cancels the conjugate determinant phase. -/
theorem sharpQutritExteriorAction_explicit_lift (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hV : Vᴴ * V = 1) (z : ℂ) (hz : z ^ 2 = V.det) :
    sharpQutritExteriorAction (z • (Vᴴ)ᵀ) = V := by
  have hd : star V.det * V.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one]
      using congrArg Matrix.det hV
  rw [sharpQutritExteriorAction_smul,
    sharpQutritExteriorAction_of_isometry _ (sharpQutrit_conjugate_isometry V hV)]
  simp only [Matrix.det_transpose, Matrix.det_conjTranspose,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.transpose_transpose, smul_smul]
  rw [hz, mul_comm, hd, one_smul]

/-- Every square root of a unitary determinant is automatically a phase. -/
theorem sharpQutrit_determinant_sqrt_phase (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hV : Vᴴ * V = 1) (z : ℂ) (hz : z ^ 2 = V.det) :
    star z * z = 1 := by
  have hd : conj V.det * V.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one,
      Complex.star_def]
      using congrArg Matrix.det hV
  have hn : Complex.normSq V.det = 1 := by
    apply Complex.ofReal_injective
    simpa only [Complex.normSq_eq_conj_mul_self, Complex.ofReal_one] using hd
  have hz2 : Complex.normSq z * Complex.normSq z = 1 := by
    simpa only [pow_two, Complex.normSq_mul, hn] using congrArg Complex.normSq hz
  have hnz : Complex.normSq z = 1 := by
    nlinarith [Complex.normSq_nonneg z]
  change conj z * z = 1
  rw [← Complex.normSq_eq_conj_mul_self, hnz]
  rfl

/-- The determinant-corrected lift satisfies the original unitary equation. -/
theorem sharpQutrit_explicit_lift_isometry (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hV : Vᴴ * V = 1) (z : ℂ) (hz : z ^ 2 = V.det) :
    (z • (Vᴴ)ᵀ)ᴴ * (z • (Vᴴ)ᵀ) = 1 := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    sharpQutrit_conjugate_isometry V hV,
    sharpQutrit_determinant_sqrt_phase V hV z hz, one_smul]

/-- Every actual unitary on the three exterior coordinates has an actual
local qutrit unitary lift, with no residual scalar phase or root premise. -/
theorem sharpQutritExteriorAction_exists_unitary_lift
    (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : Vᴴ * V = 1) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ,
      Uᴴ * U = 1 ∧ sharpQutritExteriorAction U = V := by
  obtain ⟨z, hz⟩ := Complex.isSquare V.det
  have hz2 : z ^ 2 = V.det := by simpa only [pow_two] using hz.symm
  exact ⟨z • (Vᴴ)ᵀ, sharpQutrit_explicit_lift_isometry V hV z hz2,
    sharpQutritExteriorAction_explicit_lift V hV z hz2⟩

end ThreeCopyQutritWerner
