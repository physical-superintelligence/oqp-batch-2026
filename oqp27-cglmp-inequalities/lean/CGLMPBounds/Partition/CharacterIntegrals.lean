module

public import CGLMPBounds.Partition.BoundaryBasics

@[expose] public section


/-! Exact one-dimensional integrals for the literal boundary character.
This is a prerequisite to density normalization and the count generating law;
neither multidimensional identity is assumed here. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

lemma boundaryCharacter_eq_exp_mul (n : ℕ) (t : ℝ) :
    boundaryCharacter n t =
      Complex.exp ((2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) * (t : ℂ)) := by
  unfold boundaryCharacter
  congr 1
  push_cast
  ring

lemma boundaryCharacter_zero (n : ℕ) : boundaryCharacter n 0 = 1 := by
  simp [boundaryCharacter]

lemma boundaryCharacter_one (n : ℕ) : boundaryCharacter n 1 = 1 := by
  calc
    boundaryCharacter n 1 = Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
      unfold boundaryCharacter
      congr 1
      push_cast
      ring
    _ = 1 := Complex.exp_nat_mul_two_pi_mul_I n

theorem continuous_boundaryCharacter (n : ℕ) : Continuous (boundaryCharacter n) := by
  unfold boundaryCharacter
  fun_prop

theorem integrable_boundaryCharacter_uniform (n : ℕ) :
    Integrable (boundaryCharacter n) boundaryUniformMeasure := by
  apply (integrable_const (1 : ℝ)).mono'
    (continuous_boundaryCharacter n).aestronglyMeasurable
  filter_upwards [] with t
  simp [boundaryCharacter_norm]

/-- The actual complex arc integral, with orientation retained for all x. -/
theorem intervalIntegral_boundaryCharacter (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (∫ t in (0 : ℝ)..x, boundaryCharacter n t) =
      (boundaryCharacter n x - 1) / (2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hpC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc : 2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpC) hnC) Complex.I_ne_zero
  simp_rw [boundaryCharacter_eq_exp_mul]
  rw [integral_exp_mul_complex hc]
  simp

/-- Orthogonality to constants under the actual uniform boundary measure. -/
theorem integral_boundaryCharacter_uniform (n : ℕ) (hn : 0 < n) :
    ∫ t, boundaryCharacter n t ∂boundaryUniformMeasure = 0 := by
  change (∫ t in Set.Ico (0 : ℝ) 1, boundaryCharacter n t) = 0
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    intervalIntegral_boundaryCharacter n hn 1, boundaryCharacter_one]
  simp

lemma norm_exp_two_mul_I_sub_one_sq (t : ℝ) :
    ‖Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2 =
      4 * Real.sin t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_sub]
  simp only [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I,
    norm_one, one_pow, map_one, mul_one, Complex.exp_ofReal_mul_I_re]
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- The sine-square shape is the actual squared norm of the character arc
integral. No probability/count formula is used to identify it. -/
theorem norm_intervalIntegral_boundaryCharacter_sq
    (n : ℕ) (hn : 0 < n) (x : ℝ) :
    ‖∫ t in (0 : ℝ)..x, boundaryCharacter n t‖ ^ 2 = fourierTiltShape n x := by
  have he : boundaryCharacter n x =
      Complex.exp (((2 * (Real.pi * (n : ℝ) * x) : ℝ) : ℂ) * Complex.I) := by
    unfold boundaryCharacter
    congr 1
    push_cast
    ring
  have hnum : ‖boundaryCharacter n x - 1‖ ^ 2 =
      4 * Real.sin (Real.pi * (n : ℝ) * x) ^ 2 := by
    rw [he, norm_exp_two_mul_I_sub_one_sq]
  have hden : ‖2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I‖ =
      2 * Real.pi * (n : ℝ) := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [intervalIntegral_boundaryCharacter n hn x, norm_div, div_pow, hnum, hden]
  unfold fourierTiltShape
  field_simp [Real.pi_ne_zero, hnR] <;> ring

theorem norm_integral_Ico_boundaryCharacter_sq
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) :
    ‖∫ t in Set.Ico (0 : ℝ) x, boundaryCharacter n t‖ ^ 2 =
      fourierTiltShape n x := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  exact norm_intervalIntegral_boundaryCharacter_sq n hn x

end
end CGLMPBounds.Partition
