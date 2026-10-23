module

public import CGLMPBounds.Hardy.PolynomialTwoCircleTransport

@[expose] public section


/-! Expanded literal scalar contour endpoints for independent statement
comparison: no auxiliary divided-difference definition occurs in the targets. -/

open scoped Polynomial

namespace CGLMPBounds.Hardy
noncomputable section
open Complex Metric Set

theorem polynomial_circleIntegral_eq_two_small_circles (f : ℂ[X]) {a b c : ℂ}
    (hab : a ≠ b) (p q : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (ha : a ∈ ball c R) (hb : b ∈ ball c R) :
    (∮ z in C(c, R), f.eval z / ((z - a) ^ p * (z - b) ^ q)) =
      (∮ z in C(a, ‖a - b‖ / 3), f.eval z / ((z - a) ^ p * (z - b) ^ q)) +
      (∮ z in C(b, ‖a - b‖ / 3), f.eval z / ((z - a) ^ p * (z - b) ^ q)) := by
  have h := congrArg (fun z : ℂ => z * (2 * Real.pi * Complex.I : ℂ))
    (polynomial_circleIntegral_eq_twoCircleIntegral f hab p q hR ha hb)
  simpa only [polynomialTwoCircleIntegral, div_mul_cancel₀ _ Complex.two_pi_I_ne_zero] using h

theorem polynomial_circleIntegral_eq_actual_beta (f : ℂ[X]) {a b c : ℂ}
    (hab : a ≠ b) (p q : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (ha : a ∈ ball c R) (hb : b ∈ ball c R) :
    (∮ z in C(c, R), f.eval z / ((z - a) ^ (p + 1) * (z - b) ^ (q + 1))) /
        (2 * Real.pi * Complex.I : ℂ) =
      (1 / ((p.factorial : ℂ) * q.factorial)) *
        ∫ u in (0 : ℝ)..1, (u : ℂ) ^ p * (1 - (u : ℂ)) ^ q *
          ((Polynomial.derivative^[p + q + 1]) f).eval
            ((u : ℂ) * a + (1 - (u : ℂ)) * b) :=
  polynomial_circleIntegral_eq_beta f hab p q hR ha hb

end
end CGLMPBounds.Hardy
