module

public import CGLMPBounds.Hardy.RootFractions

@[expose] public section


/-!
# A finite determinant proof of the trace-resolvent formula

Factor `det((ζ+t)I-A)` around an invertible `ζI-A`, then use Mathlib's
`derivative_det_one_add_X_smul`. This is a polynomial identity argument and
does not require diagonalizability or any choice of eigenvectors.
-/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Polynomial
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma eval_det_one_add_X_smul (N : Matrix ι ι ℂ) (t : ℂ) :
    (Matrix.det (1 + (X : ℂ[X]) • N.map C)).eval t =
      Matrix.det (1 + t • N) := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Polynomial.coe_evalRingHom,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  by_cases h : i = j
  · simp only [h, ite_true, Polynomial.eval_one]
  · simp only [h, ite_false, Polynomial.eval_zero]

/-- Exact local polynomial factorization around a nonsingular scalar shift. -/
lemma charpoly_translate_factor (A : Matrix ι ι ℂ) (ζ : ℂ)
    (hdet : IsUnit (Matrix.scalar ι ζ - A).det) :
    A.charpoly.comp (X + C ζ) =
      C (Matrix.scalar ι ζ - A).det *
        Matrix.det (1 + (X : ℂ[X]) • ((Matrix.scalar ι ζ - A)⁻¹).map C) := by
  let M := Matrix.scalar ι ζ - A
  have hM : IsUnit M.det := hdet
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C,
    eval_det_one_add_X_smul, Matrix.eval_charpoly, ← Matrix.det_mul]
  change (Matrix.scalar ι (t + ζ) - A).det = (M * (1 + t • M⁻¹)).det
  congr 1
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_nonsing_inv M hM]
  ext i j
  by_cases h : i = j
  · subst j
    simp [M, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    <;> ring
  · simp [M, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, h]

/-- Jacobi's trace identity in the precise scalar-shift form needed here. -/
lemma charpoly_derivative_eq_det_mul_trace_inverse (A : Matrix ι ι ℂ) (ζ : ℂ)
    (hdet : IsUnit (Matrix.scalar ι ζ - A).det) :
    A.charpoly.derivative.eval ζ =
      (Matrix.scalar ι ζ - A).det * Matrix.trace (Matrix.scalar ι ζ - A)⁻¹ := by
  have h := congrArg (fun p : ℂ[X] => p.derivative.eval 0)
    (charpoly_translate_factor A ζ hdet)
  simpa only [Polynomial.derivative_comp, Polynomial.derivative_add,
    Polynomial.derivative_X, Polynomial.derivative_C, add_zero, one_mul,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    zero_add, Polynomial.derivative_C_mul, Polynomial.eval_mul,
    Matrix.derivative_det_one_add_X_smul] using h

lemma scalar_shift_det_isUnit (A : Matrix ι ι ℂ) {ζ : ℂ}
    (hζ : ζ ∉ spectrum ℂ A) : IsUnit (Matrix.scalar ι ζ - A).det := by
  have hu : IsUnit (algebraMap ℂ (Matrix ι ι ℂ) ζ - A) := by
    simpa only [spectrum.mem_iff, not_not] using hζ
  exact (Matrix.scalar ι ζ - A).isUnit_iff_isUnit_det.mp hu

lemma resolvent_eq_matrix_inverse (A : Matrix ι ι ℂ) (ζ : ℂ) :
    resolvent A ζ = (Matrix.scalar ι ζ - A)⁻¹ :=
  (Matrix.nonsing_inv_eq_ringInverse (Matrix.scalar ι ζ - A)).symm

/-- The scalar trace of the actual resolvent is the logarithmic derivative
of the characteristic polynomial at every point outside the spectrum. -/
theorem trace_resolvent_eq_logDerivative (A : Matrix ι ι ℂ) {ζ : ℂ}
    (hζ : ζ ∉ spectrum ℂ A) :
    Matrix.trace (resolvent A ζ) = A.charpoly.derivative.eval ζ / A.charpoly.eval ζ := by
  rw [resolvent_eq_matrix_inverse]
  apply (eq_div_iff (charpoly_eval_ne_zero_of_not_mem_spectrum A hζ)).2
  have h := charpoly_derivative_eq_det_mul_trace_inverse A ζ (scalar_shift_det_isUnit A hζ)
  simpa only [Matrix.eval_charpoly, mul_comm] using h.symm

/-- Root-multiset trace-resolvent identity, valid for defective matrices. -/
theorem trace_resolvent_eq_root_sum (A : Matrix ι ι ℂ) {ζ : ℂ}
    (hζ : ζ ∉ spectrum ℂ A) :
    Matrix.trace (resolvent A ζ) =
      (A.charpoly.roots.map (fun a => 1 / (ζ - a))).sum := by
  rw [trace_resolvent_eq_logDerivative A hζ, charpoly_logDerivative_eq_root_sum A hζ]

end
end CGLMPBounds.Hardy
