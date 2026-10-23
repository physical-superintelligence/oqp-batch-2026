module

public import CGLMPBounds.Defs.ScalarBeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

@[expose] public section


/-!
# Actual polynomial moments of the source beta transform

Reuse the proved beta/gamma integral and gamma's natural-number values. These
lemmas concern Bochner integrals, not a transform defined through its moments.
-/

namespace CGLMPBounds.Certificates

theorem integral_power_one_sub_power (p q : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ p * (1 - x) ^ q) =
      (p.factorial : ℝ) * q.factorial / (p + q + 1).factorial := by
  have hb := Complex.betaIntegral_eq_Gamma_mul_div ((p : ℂ) + 1) ((q : ℂ) + 1)
    (by simp; positivity) (by simp; positivity)
  have hi : Complex.betaIntegral ((p : ℂ) + 1) ((q : ℂ) + 1) =
      ((∫ x in (0 : ℝ)..1, x ^ p * (1 - x) ^ q : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    simp only [add_sub_cancel_right, Complex.cpow_natCast]
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub,
      Complex.ofReal_one]
  have hadd : (p : ℂ) + 1 + ((q : ℂ) + 1) = ((p + q + 1 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  rw [hi, hadd, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial] at hb
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast] using hb

/-- Exact factorial evaluation for every polynomial moment of B_d. -/
theorem scalarBetaTransform_power (d h k : ℕ) :
    scalarBetaTransform d h (fun x => (1 - x) ^ k) =
      (d : ℝ) * (d.choose h : ℝ) * h.factorial * (d - h + k).factorial /
        (h + (d - h + k) + 1).factorial := by
  unfold scalarBetaTransform scalarBinomialWeight
  have hi : (∫ x in (0 : ℝ)..1,
      (d.choose h : ℝ) * x ^ h * (1 - x) ^ (d - h) * (1 - x) ^ k) =
      (d.choose h : ℝ) * ∫ x in (0 : ℝ)..1, x ^ h * (1 - x) ^ (d - h + k) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [pow_add]
    ring
  rw [hi, integral_power_one_sub_power]
  ring

theorem scalarBetaMoment_succ (d h k : ℕ) :
    scalarBetaMoment d h (k + 1) = scalarBetaMoment d h k *
      (((d : ℝ) - h + k + 1) / ((d : ℝ) + k + 2)) := by
  simp only [scalarBetaMoment, Finset.prod_range_succ]
  ring

/-- The source rising-product moment equals the factorial moment. -/
theorem scalarBetaMoment_factorial (d h k : ℕ) (hh : h ≤ d) :
    scalarBetaMoment d h k =
      (d : ℝ) * (d.choose h : ℝ) * h.factorial * (d - h + k).factorial /
        (d + k + 1).factorial := by
  induction k with
  | zero =>
    have hc : (d.choose h : ℝ) * h.factorial * (d - h).factorial = d.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hh
    simp only [scalarBetaMoment, Finset.range_zero, Finset.prod_empty, mul_one,
      Nat.add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
    have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
    calc
      _ = (d : ℝ) * d.factorial / (((d : ℝ) + 1) * d.factorial) := by
        field_simp [hfac, hd1]
        <;> ring
      _ = _ := by rw [← hc]; ring
  | succ k ih =>
    rw [scalarBetaMoment_succ, ih]
    rw [show d - h + (k + 1) = (d - h + k) + 1 by omega,
      show d + (k + 1) + 1 = (d + k + 1) + 1 by omega]
    rw [Nat.factorial_succ (d - h + k), Nat.factorial_succ (d + k + 1)]
    push_cast [Nat.cast_sub hh]
    have hfac : ((d + k + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (d + k + 1)
    have hden : (d : ℝ) + k + 2 ≠ 0 := by positivity
    field_simp [hfac, hden]
    <;> ring

/-- The product formula in Appendix I is the actual integral moment. -/
theorem scalarBetaTransform_power_eq_moment (d h k : ℕ) (hh : h ≤ d) :
    scalarBetaTransform d h (fun x => (1 - x) ^ k) = scalarBetaMoment d h k := by
  rw [scalarBetaTransform_power, scalarBetaMoment_factorial d h k hh]
  rw [show h + (d - h + k) + 1 = d + k + 1 by omega]

theorem scalarBetaTransform_one (d h : ℕ) (hh : h ≤ d) :
    scalarBetaTransform d h (fun _ => 1) = (d : ℝ) / ((d : ℝ) + 1) := by
  simpa only [pow_zero, scalarBetaMoment, Finset.range_zero,
    Finset.prod_empty, mul_one] using scalarBetaTransform_power_eq_moment d h 0 hh

/-- Exact pole cancellation used in I.5. Endpoint values of the totalized
reciprocal are harmless because the integral identity is proved on (0,1). -/
theorem scalarBetaTransform_pole (d h : ℕ) (hh : h < d) :
    scalarBetaTransform d h (fun x => 1 / (1 - x)) = (d : ℝ) / ((d : ℝ) - h) := by
  let q := d - h - 1
  have hq : q + 1 = d - h := by dsimp [q]; omega
  have hdq : h + q + 1 = d := by dsimp [q]; omega
  have hi : (∫ x in (0 : ℝ)..1, scalarBinomialWeight d h x * (1 / (1 - x))) =
      (d.choose h : ℝ) * ∫ x in (0 : ℝ)..1, x ^ h * (1 - x) ^ q := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    unfold scalarBinomialWeight
    dsimp only
    rw [← hq, pow_succ]
    field_simp [hx1]
    <;> ring
  unfold scalarBetaTransform
  rw [hi, integral_power_one_sub_power, hdq]
  have hc : (d.choose h : ℝ) * h.factorial * (d - h).factorial = d.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hh.le
  rw [← hq, Nat.factorial_succ] at hc
  push_cast at hc
  have hqn : (q : ℝ) + 1 = (d : ℝ) - h := by
    rw [← Nat.cast_sub hh.le]
    exact_mod_cast hq
  rw [hqn] at hc
  have hden : (d : ℝ) - h ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (by exact_mod_cast hh))
  have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hcm := congrArg (fun t : ℝ => (d : ℝ) * t) hc
  field_simp [hden, hfac]
  <;> nlinarith [hcm]

end CGLMPBounds.Certificates
