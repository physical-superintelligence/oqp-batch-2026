module

public import CGLMPBounds.Certificates.ScalarEta
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section


/-!
# The uniform geometric bound on the printed coefficients

The exact Bernoulli/eta identity is derived from Mathlib's zeta-value theorem,
followed by the strict alternating-series bound. Identifying the resulting
power series with the cosecant function remains a separate analytic obligation.
-/

namespace CGLMPBounds.Certificates

/-- The eta identity displayed before (J.3), for the exact formula in (I.1). -/
theorem scalarCosecantCoefficient_eq_eta (n : ℕ) (hn : n ≠ 0) :
    scalarCosecantCoefficient n = (4 / Real.pi) * (1 / 4 : ℝ) ^ n * scalarEta n := by
  rw [scalarEta_eq_zeta_factor n hn, scalar_zeta_eq_abs_bernoulli n hn]
  unfold scalarCosecantCoefficient
  have hk : 2 * n - 1 + 1 = 2 * n := by omega
  have htwo : (2 : ℝ) ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
    conv_lhs => rw [← hk, pow_succ]
    ring
  have hpi : Real.pi ^ (2 * n) = Real.pi * Real.pi ^ (2 * n - 1) := by
    conv_lhs => rw [← hk, pow_succ]
    ring
  have hfour : (1 / 4 : ℝ) ^ n = 1 / (2 : ℝ) ^ (2 * n) := by
    rw [div_pow, one_pow, pow_mul]
    norm_num
  rw [hfour, htwo, hpi, div_pow]
  have hfac : ((2 * n).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  field_simp [Real.pi_ne_zero, hfac]
  <;> ring

/-- Positivity and the geometric bound used for every omitted term in (J.3). -/
theorem scalarCosecantCoefficient_pos_lt (n : ℕ) (hn : n ≠ 0) :
    0 < scalarCosecantCoefficient n ∧
      scalarCosecantCoefficient n < (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ n := by
  rw [scalarCosecantCoefficient_eq_eta n hn]
  have hη := scalarEta_mem_Ioo n hn
  have hpow : 0 < (1 / 4 : ℝ) ^ n := by positivity
  have hpi : 0 < 4 / Real.pi := by positivity
  have hscale : 4 / Real.pi < (4 / 3 : ℝ) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) Real.pi_gt_three
  constructor
  · exact mul_pos (mul_pos hpi hpow) hη.1
  · calc
      _ < (4 / Real.pi) * (1 / 4 : ℝ) ^ n :=
        mul_lt_of_lt_one_right (mul_pos hpi hpow) hη.2
      _ < _ := mul_lt_mul_of_pos_right hscale hpow

end CGLMPBounds.Certificates
