module

public import CGLMPBounds.Certificates.ScalarCotangent
public import CGLMPBounds.Certificates.ScalarCoefficientBound

@[expose] public section


/-!
# Analytic identification of the printed Bernoulli coefficients

Derive the cosecant generating function from convergent cotangent series.
The scalar value at zero uses Lean's total division, and the series vanishes
there termwise, agreeing with the removable value of the regularized function.
-/

namespace CGLMPBounds.Certificates

theorem cot_half_sub_cot {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Real.cot (t / 2) - Real.cot t = 1 / Real.sin t := by
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  have hh : Real.sin (t / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])).ne'
  have hhalf : 2 * (t / 2) = t := by ring
  have hsin : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    simpa only [hhalf] using Real.sin_two_mul (t / 2)
  have hcos : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
    simpa only [hhalf] using Real.cos_two_mul (t / 2)
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  field_simp [hs, hh]
  rw [hsin, hcos]
  ring

/-- Exact coefficient conversion for subtracting the two cotangent series. -/
lemma scalarCosecantCoefficient_power (n : ℕ) (hn : n ≠ 0) (x : ℝ) :
    scalarCosecantCoefficient n * (2 * x) ^ (2 * n - 1) =
      (2 / Real.pi) *
        (x ^ (2 * n - 1) * (∑' j : ℕ, 1 / (j : ℝ) ^ (2 * n)) -
          (x / 2) ^ (2 * n - 1) * (∑' j : ℕ, 1 / (j : ℝ) ^ (2 * n))) := by
  rw [scalarCosecantCoefficient_eq_eta n hn, scalarEta_eq_zeta_factor n hn]
  have hk : 2 * n - 1 + 1 = 2 * n := by omega
  have htwo : (2 : ℝ) ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
    conv_lhs => rw [← hk, pow_succ]
    ring
  have hfour : (1 / 4 : ℝ) ^ n = 1 / (2 : ℝ) ^ (2 * n) := by
    rw [div_pow, one_pow, pow_mul]
    norm_num
  rw [hfour, htwo, mul_pow, div_pow]
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- The regularized cosecant expansion on its positive convergence interval.
All coefficients are the source's explicit Bernoulli formula, not assumed
Taylor coefficients or unknown witnesses. -/
theorem scalar_cosecant_hasSum {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 2) :
    HasSum (fun k : ℕ => scalarCosecantCoefficient (k + 1) * y ^ (2 * k + 1))
      (1 / Real.sin (Real.pi * y / 2) - 2 / (Real.pi * y)) := by
  have hx : y / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have hh : (y / 2) / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have h := ((cotangent_power_hasSum hx).sub (cotangent_power_hasSum hh)).mul_left
    (2 / Real.pi)
  have hterm (k : ℕ) : scalarCosecantCoefficient (k + 1) * y ^ (2 * k + 1) =
      (2 / Real.pi) *
        ((y / 2) ^ (2 * k + 1) * (∑' j : ℕ, 1 / (j : ℝ) ^ (2 * (k + 1))) -
          (y / 2 / 2) ^ (2 * k + 1) *
            (∑' j : ℕ, 1 / (j : ℝ) ^ (2 * (k + 1)))) := by
    have hh := scalarCosecantCoefficient_power (k + 1) (by omega) (y / 2)
    simpa only [show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      show 2 * (y / 2) = y by ring] using hh
  have ht : Real.pi * (y / 2) ∈ Set.Ioo (0 : ℝ) Real.pi := by
    constructor
    · exact mul_pos Real.pi_pos hx.1
    · nlinarith [Real.pi_pos, hx.2]
  have hc := cot_half_sub_cot ht
  have harg : Real.pi * (y / 2 / 2) = Real.pi * (y / 2) / 2 := by ring
  have hmain : Real.pi * y / 2 = Real.pi * (y / 2) := by ring
  have hy0 : y ≠ 0 := hy.1.ne'
  convert h using 1
  · ext k
    exact hterm k
  · rw [harg]
    rw [show Real.cot (Real.pi * (y / 2) / 2) =
      Real.cot (Real.pi * (y / 2)) + 1 / Real.sin (Real.pi * (y / 2)) by linarith [hc]]
    rw [hmain]
    field_simp [Real.pi_ne_zero, hy0]
    <;> ring

/-- Including the removable endpoint at zero, as used by the scalar certificate. -/
theorem scalar_cosecant_hasSum_zero_le {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 2) :
    HasSum (fun k : ℕ => scalarCosecantCoefficient (k + 1) * y ^ (2 * k + 1))
      (1 / Real.sin (Real.pi * y / 2) - 2 / (Real.pi * y)) := by
  rcases eq_or_lt_of_le hy.1 with hzero | hpos
  · subst y
    simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  · exact scalar_cosecant_hasSum ⟨hpos, hy.2⟩

end CGLMPBounds.Certificates
