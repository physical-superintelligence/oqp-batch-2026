module

public import CGLMPBounds.Hardy.SchwarzPositiveNegativeContours
public import CGLMPBounds.Hardy.SchwarzMomentCoefficients

@[expose] public section


/-! The full literal C.7 trace-density moment identity. The real density
moment and the positive-part trace are independent manuscript definitions;
the bridge passes through the actual q analytic germ, proved contour
inversion, and proved negative/positive cancellation. No moment, coefficient,
residue, analyticity or contour conclusion is a premise of either endpoint. -/

open Complex
open scoped Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- Moment form of C.7, expressed through the literal derivative/factorial
Taylor coefficient of the genuine positive part. -/
theorem traceDensity_moment_eq_positiveTraceTaylorCoefficient
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (m : ℕ) :
    (∫ x : ℝ, x ^ m * traceDensity H Y x) =
      positiveTraceTaylorCoefficient H Y (m + 1) (m + 2) / ((m + 1 : ℕ) : ℝ) := by
  have hc := positiveTraceTaylorCoefficient_eq_mul_exteriorTaylorCoefficient
    hH hY hdet (by omega : 2 ≤ m + 2)
  have hn : m + 2 - 1 = m + 1 := by omega
  rw [hn, ← traceDensity_moment_eq_exteriorTaylorCoefficient hH hY hdet m] at hc
  have hr : positiveTraceTaylorCoefficient H Y (m + 1) (m + 2) =
      ((m + 1 : ℕ) : ℝ) * (∫ x : ℝ, x ^ m * traceDensity H Y x) := by
    exact_mod_cast hc
  apply (eq_div_iff (by positivity : ((m + 1 : ℕ) : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using hr.symm

/-- Exactly the full-line moment and real derivative identity printed in
C.7, including (m+1)(m+2)! and normalized matrix trace. -/
theorem traceDensity_moment_eq_positiveTrace_derivative
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (m : ℕ) :
    (∫ x : ℝ, x ^ m * traceDensity H Y x) =
      (1 / (((m + 1 : ℕ) : ℝ) * ((m + 2).factorial : ℝ))) *
        iteratedDeriv (m + 2)
          (fun t : ℝ => positiveTracePower (H + (t : ℂ) • Y) (m + 1)) 0 := by
  rw [traceDensity_moment_eq_positiveTraceTaylorCoefficient hH hY hdet m,
    positiveTraceTaylorCoefficient]
  ring

end
end CGLMPBounds.Hardy
