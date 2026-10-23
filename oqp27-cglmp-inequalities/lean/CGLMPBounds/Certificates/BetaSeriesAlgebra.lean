module

public import CGLMPBounds.Certificates.BetaMoments
public import CGLMPBounds.Certificates.ScalarSmooth

@[expose] public section


/-!
# Polynomial algebra for the integral-to-series identity (I.2)

All integrals in these identities are literal source beta integrals.
-/

namespace CGLMPBounds.Certificates
noncomputable section

theorem scalarBinomialWeight_continuous (d h : ℕ) : Continuous (scalarBinomialWeight d h) := by
  unfold scalarBinomialWeight
  fun_prop

theorem scalarBinomialWeight_bound (d h : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : ‖scalarBinomialWeight d h x‖ ≤ (d.choose h : ℝ) := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
  have hp : x ^ h ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hq : (1 - x) ^ (d - h) ≤ 1 := pow_le_one₀ hx1 (by linarith [hx.1])
  rw [scalarBinomialWeight, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (d.choose h : ℝ) * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hq (by positivity) (by positivity)
    _ = _ := by ring

theorem scalarBetaTransform_const_mul (d h : ℕ) (a : ℝ) (g : ℝ → ℝ) :
    scalarBetaTransform d h (fun x => a * g x) = a * scalarBetaTransform d h g := by
  unfold scalarBetaTransform
  simp_rw [mul_left_comm (scalarBinomialWeight d h _) a]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem scalarBetaTransform_sub (d h : ℕ) (f g : ℝ → ℝ)
    (hf : IntervalIntegrable (fun x => scalarBinomialWeight d h x * f x)
      MeasureTheory.volume 0 1)
    (hg : IntervalIntegrable (fun x => scalarBinomialWeight d h x * g x)
      MeasureTheory.volume 0 1) :
    scalarBetaTransform d h (fun x => f x - g x) =
      scalarBetaTransform d h f - scalarBetaTransform d h g := by
  unfold scalarBetaTransform
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hf hg]
  ring

theorem scalarPhiTerm_two (i : ℕ) (y : ℝ) :
    scalarPhiTerm i 2 y = scalarCosecantCoefficient (i + 1) *
      (((2 * i : ℝ) + 1) * ((2 * i : ℝ) + 2) * y ^ (2 * i) -
        ((2 * i : ℝ) + 2) * ((2 * i : ℝ) + 3) * y ^ (2 * i + 1)) := by
  unfold scalarPhiTerm scalarPowerDerivative
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one,
    show 2 * i + 2 - 1 = 2 * i + 1 by omega,
    show 2 * i + 3 - 1 = 2 * i + 2 by omega,
    show 2 * i + 2 - 2 = 2 * i by omega,
    show 2 * i + 3 - 2 = 2 * i + 1 by omega]
  push_cast
  ring

/-- Integrate the reflected second derivative of one polynomial summand. -/
theorem scalarBetaTransform_phiTerm_two (d h i : ℕ) (hh : h ≤ d) :
    scalarBetaTransform d h (fun x => scalarPhiTerm i 2 (1 - x)) =
      scalarCosecantCoefficient (i + 1) *
        (((2 * i : ℝ) + 1) * ((2 * i : ℝ) + 2) * scalarBetaMoment d h (2 * i) -
          ((2 * i : ℝ) + 2) * ((2 * i : ℝ) + 3) * scalarBetaMoment d h (2 * i + 1)) := by
  simp_rw [scalarPhiTerm_two]
  rw [scalarBetaTransform_const_mul]
  rw [scalarBetaTransform_sub]
  · rw [scalarBetaTransform_const_mul, scalarBetaTransform_const_mul,
      scalarBetaTransform_power_eq_moment d h (2 * i) hh,
      scalarBetaTransform_power_eq_moment d h (2 * i + 1) hh]
  · apply Continuous.intervalIntegrable
    unfold scalarBinomialWeight
    fun_prop
  · apply Continuous.intervalIntegrable
    unfold scalarBinomialWeight
    fun_prop

end
end CGLMPBounds.Certificates
