module

public import CGLMPBounds.Hardy.PositivePinchingMonomials

@[expose] public section


/-! The literal polynomial trace identity C.10 for the actual C.11 measure.
Finite linearity extends the reconstructed monomial identity to every complex
polynomial, with all integrability obligations supplied by the density bound. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Polynomial MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normalizedPolynomialTrace_eq_sum_trace (f : ℂ[X]) (A : Matrix ι ι ℂ) :
    normalizedPolynomialTrace f A =
      ∑ k ∈ f.support, f.coeff k * (Matrix.trace (A ^ k) / (Fintype.card ι : ℂ)) := by
  unfold normalizedPolynomialTrace
  rw [Matrix.trace_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.trace_smul, smul_eq_mul]
  ring

lemma polynomial_second_derivative_support_expansion (f : ℂ[X]) :
    f.derivative.derivative =
      ∑ k ∈ f.support, C (f.coeff k) * (X ^ k : ℂ[X]).derivative.derivative := by
  conv_lhs => rw [f.as_sum_support_C_mul_X_pow]
  simp only [Polynomial.derivative_sum, Polynomial.derivative_C_mul]

theorem positivePinching_polynomial_identity [Nonempty ι]
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) (f : ℂ[X]) (s t : ℂ) :
    normalizedPolynomialTrace f (s • B + t • Y) -
      normalizedPolynomialTrace f (s • B + t • positivePinchingPart B Y) =
      t ^ 2 * ∫ p : ℝ × ℝ, f.derivative.derivative.eval (-s * p.1 + t * p.2)
        ∂positivePinchingMeasure B Y := by
  have hfun : (fun p : ℝ × ℝ => f.derivative.derivative.eval (-s * p.1 + t * p.2)) =
      (fun p => ∑ k ∈ f.support, f.coeff k *
        (X ^ k : ℂ[X]).derivative.derivative.eval (-s * p.1 + t * p.2)) := by
    funext p
    rw [polynomial_second_derivative_support_expansion]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  have hI : ∀ k ∈ f.support, Integrable (fun p : ℝ × ℝ => f.coeff k *
      (X ^ k : ℂ[X]).derivative.derivative.eval (-s * p.1 + t * p.2))
        (positivePinchingMeasure B Y) := by
    intro k _
    exact (positivePinching_polynomial_second_derivative_integrable hB hB2 hY
      (X ^ k) s t).const_mul (f.coeff k)
  rw [normalizedPolynomialTrace_eq_sum_trace, normalizedPolynomialTrace_eq_sum_trace,
    ← Finset.sum_sub_distrib, hfun, integral_finsetSum f.support hI, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_sub, positivePinching_monomial hB hB2 hY k s t, integral_const_mul]
  ring

/-- C.10 together with its actual Bochner-integrability obligation. -/
theorem positivePinching_polynomial_identity_integrable [Nonempty ι]
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) (f : ℂ[X]) (s t : ℂ) :
    Integrable (fun p : ℝ × ℝ => f.derivative.derivative.eval (-s * p.1 + t * p.2))
      (positivePinchingMeasure B Y) ∧
    normalizedPolynomialTrace f (s • B + t • Y) -
      normalizedPolynomialTrace f (s • B + t • positivePinchingPart B Y) =
      t ^ 2 * ∫ p : ℝ × ℝ, f.derivative.derivative.eval (-s * p.1 + t * p.2)
        ∂positivePinchingMeasure B Y :=
  ⟨positivePinching_polynomial_second_derivative_integrable hB hB2 hY f s t,
    positivePinching_polynomial_identity hB hB2 hY f s t⟩

end
end CGLMPBounds.Hardy
