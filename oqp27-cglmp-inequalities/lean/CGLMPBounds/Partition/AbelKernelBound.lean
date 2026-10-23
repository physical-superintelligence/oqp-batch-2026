module

public import CGLMPBounds.Partition.AbelPairKernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section


/-! Uniform endpoint control for the genuine Abel kernel, needed for the
D.2 integration limit. The remaining two-interval integrability statement
is not assumed here. -/

namespace CGLMPBounds.Partition
open Set
noncomputable section

lemma quarterBranch_denominator_norm_sq (q x : ℝ) :
    ‖1 - (q : ℂ) * Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      (1 - q) ^ 2 + 4 * q * Real.sin (Real.pi * x) ^ 2 := by
  calc
    _ = 1 + q ^ 2 - 2 * q * Real.cos (2 * Real.pi * x) := by
      rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one,
        Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
        Complex.norm_exp_ofReal_mul_I]
      simp only [one_pow, mul_one, one_mul, Complex.conj_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.exp_ofReal_mul_I_re]
      ring
    _ = _ := by
      rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring,
        Real.cos_two_mul_eq_one_sub]
      ring

lemma quarterBranch_denominator_norm_lower (q : ℝ) (hq : (1 / 2 : ℝ) ≤ q)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.sin (Real.pi * x) ≤
      ‖1 - (q : ℂ) * Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)‖ := by
  have hs : 0 < Real.sin (Real.pi * x) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos hx.1
    · simpa only [mul_one] using mul_lt_mul_of_pos_left hx.2 Real.pi_pos
  have hp : 0 ≤ (4 * q - 1) * Real.sin (Real.pi * x) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have he := quarterBranch_denominator_norm_sq q x
  have hn := norm_nonneg
    (1 - (q : ℂ) * Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
  nlinarith [sq_nonneg (1 - q)]

theorem quarterBranchAbelKernel_norm_le_cosecant (q : ℝ)
    (hq₀ : (1 / 2 : ℝ) ≤ q) (hq₁ : q < 1)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖quarterBranchAbelKernel q x‖ ≤ 1 / Real.sin (Real.pi * x) := by
  have hs : 0 < Real.sin (Real.pi * x) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos hx.1
    · simpa only [mul_one] using mul_lt_mul_of_pos_left hx.2 Real.pi_pos
  rw [quarterBranchAbelKernel_eq q x (by linarith) hq₁, norm_div,
    Complex.norm_exp_ofReal_mul_I]
  exact one_div_le_one_div_of_le hs (quarterBranch_denominator_norm_lower q hq₀ hx)

lemma cosecant_le_endpoint_poles {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    1 / Real.sin (Real.pi * x) ≤ 1 / (2 * x) + 1 / (2 * (1 - x)) := by
  have hx₀ : 0 < x := hx.1
  have hleft : 0 < 1 - x := sub_pos.mpr hx.2
  by_cases hh : x ≤ 1 / 2
  · have hs := Real.mul_le_sin (x := Real.pi * x) (by positivity)
      (by nlinarith [Real.pi_pos])
    have he : 2 / Real.pi * (Real.pi * x) = 2 * x := by
      field_simp [Real.pi_ne_zero]
    rw [he] at hs
    calc
      _ ≤ 1 / (2 * x) := one_div_le_one_div_of_le (by positivity) hs
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hright : 1 - x ≤ 1 / 2 := by linarith
    have hs := Real.mul_le_sin (x := Real.pi * (1 - x)) (by positivity)
      (by nlinarith [Real.pi_pos])
    have he : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by
      field_simp [Real.pi_ne_zero]
    rw [he, show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring,
      Real.sin_pi_sub] at hs
    calc
      _ ≤ 1 / (2 * (1 - x)) := one_div_le_one_div_of_le (by positivity) hs
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-- A single elementary majorant for the two possible endpoint singularities. -/
theorem quarterBranchAbelKernel_norm_le_endpoint_poles (q : ℝ)
    (hq₀ : (1 / 2 : ℝ) ≤ q) (hq₁ : q < 1)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖quarterBranchAbelKernel q x‖ ≤ 1 / (2 * x) + 1 / (2 * (1 - x)) :=
  (quarterBranchAbelKernel_norm_le_cosecant q hq₀ hq₁ hx).trans
    (cosecant_le_endpoint_poles hx)

end
end CGLMPBounds.Partition
