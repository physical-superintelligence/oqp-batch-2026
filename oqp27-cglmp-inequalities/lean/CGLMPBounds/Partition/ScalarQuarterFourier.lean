module

public import CGLMPBounds.Partition.HardyConstantSeries

@[expose] public section


/-! Actual Fourier coefficients of the scalar quarter-root branch used
in D.2–D.4. Direct integration gives the source negative energy, including
its precise Catalan normalization. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

theorem scalar_quarter_negative_coefficient (n : ℕ) :
    (∫ t in (0 : ℝ)..1,
      Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-Real.pi * t / 2 : ℝ) : ℂ) * Complex.I)) =
      (2 : ℂ) * (Complex.I - 1) / ((Real.pi : ℂ) * (4 * (n : ℂ) + 3)) := by
  let c : ℂ := ((Real.pi : ℂ) / 2) * (4 * (n : ℂ) + 3) * Complex.I
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hnR : (4 * (n : ℝ) + 3) ≠ 0 := by positivity
  have hn : 4 * (n : ℂ) + 3 ≠ 0 := by exact_mod_cast hnR
  have hc : c ≠ 0 := mul_ne_zero
    (mul_ne_zero (div_ne_zero hp (by norm_num)) hn) Complex.I_ne_zero
  have he : (fun t : ℝ =>
      Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-Real.pi * t / 2 : ℝ) : ℂ) * Complex.I)) =
      (fun t : ℝ => Complex.exp (c * (t : ℂ))) := by
    funext t
    rw [← Complex.exp_add]
    congr 1
    dsimp [c]
    push_cast
    ring
  have hce : Complex.exp c = -Complex.I := by
    have harg : c = ((n + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
        (-(Real.pi : ℂ) / 2 * Complex.I) := by
      dsimp [c]
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I,
      Complex.exp_neg_pi_div_two_mul_I, one_mul]
  rw [he, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, hce]
  dsimp [c]
  field_simp [hp, hn, Complex.I_ne_zero]
  <;> ring_nf
  <;> norm_num [Complex.I_sq]
  <;> ring

theorem scalar_quarter_negative_coefficient_norm_sq (n : ℕ) :
    ‖∫ t in (0 : ℝ)..1,
      Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-Real.pi * t / 2 : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      (8 / Real.pi ^ 2) * (1 / (4 * (n : ℝ) + 3) ^ 2) := by
  rw [scalar_quarter_negative_coefficient]
  have hi : ‖Complex.I - 1‖ ^ 2 = 2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [Real.pi_pos.le]
  have hn : ‖4 * (n : ℂ) + 3‖ = 4 * (n : ℝ) + 3 := by
    rw [show 4 * (n : ℂ) + 3 = ((4 * (n : ℝ) + 3 : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.norm_of_nonneg (by positivity)
  rw [norm_div, norm_mul, norm_mul, hp, hn, div_pow, mul_pow, hi, mul_pow]
  norm_num
  <;> field_simp [Real.pi_ne_zero,
    (show 4 * (n : ℝ) + 3 ≠ 0 by positivity)]
  <;> ring

/-- The scalar branch has exactly the ν₄ energy printed after D.3. -/
theorem scalar_quarter_negative_energy :
    (∑' n : ℕ, ‖∫ t in (0 : ℝ)..1,
      Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-Real.pi * t / 2 : ℝ) : ℂ) * Complex.I)‖ ^ 2) =
      sourceFourthRootHardyConstant := by
  simp_rw [scalar_quarter_negative_coefficient_norm_sq]
  rw [tsum_mul_left, sourceFourthRootHardyConstant_eq_positive_series]

end
end CGLMPBounds.Partition
