module

public import CGLMPBounds.Defs.PartitionCurvature
public import CGLMPBounds.Partition.MixtureCountLaw

@[expose] public section


/-! Actual first and second derivatives of the positive Fourier mixture's
shape. Global summable derivative bounds justify both termwise derivatives. -/

namespace CGLMPBounds.Partition
noncomputable section

lemma hasDerivAt_fourierTiltShape (n : ℕ) (hn : 0 < n) (x : ℝ) :
    HasDerivAt (fourierTiltShape n) (fourierTiltSlope n x) x := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hlin : HasDerivAt (fun y : ℝ => Real.pi * (n : ℝ) * y)
      (Real.pi * (n : ℝ)) x := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id x).const_mul (Real.pi * (n : ℝ))
  change HasDerivAt (fun y : ℝ =>
    Real.sin (Real.pi * (n : ℝ) * y) ^ 2 / (Real.pi ^ 2 * (n : ℝ) ^ 2)) _ x
  convert (hlin.sin.pow 2).div_const (Real.pi ^ 2 * (n : ℝ) ^ 2) using 1
  unfold fourierTiltSlope
  rw [show 2 * Real.pi * (n : ℝ) * x = 2 * (Real.pi * (n : ℝ) * x) by ring,
    Real.sin_two_mul]
  field_simp [Real.pi_ne_zero, hn0]
  ring

lemma hasDerivAt_fourierTiltSlope (n : ℕ) (hn : 0 < n) (x : ℝ) :
    HasDerivAt (fourierTiltSlope n)
      (2 * Real.cos (2 * Real.pi * (n : ℝ) * x)) x := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hlin : HasDerivAt (fun y : ℝ => 2 * Real.pi * (n : ℝ) * y)
      (2 * Real.pi * (n : ℝ)) x := by
    simpa only [mul_one, id_eq] using
      (hasDerivAt_id x).const_mul (2 * Real.pi * (n : ℝ))
  change HasDerivAt (fun y : ℝ =>
    Real.sin (2 * Real.pi * (n : ℝ) * y) / (Real.pi * (n : ℝ))) _ x
  convert hlin.sin.div_const (Real.pi * (n : ℝ)) using 1
  field_simp [Real.pi_ne_zero, hn0]

lemma norm_fourierTiltSlope_succ_le_one (n : ℕ) (x : ℝ) :
    ‖fourierTiltSlope (n + 1) x‖ ≤ 1 := by
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hp : (1 : ℝ) ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
  have hden : (1 : ℝ) ≤ Real.pi * ((n + 1 : ℕ) : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hn)]
  rw [fourierTiltSlope, norm_div, Real.norm_eq_abs,
    Real.norm_of_nonneg (le_trans zero_le_one hden)]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).mpr
  simpa only [one_mul] using (Real.abs_sin_le_one _).trans hden

lemma norm_weighted_fourierTiltSlope_le (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (n : ℕ) (x : ℝ) :
    ‖a n * fourierTiltSlope (n + 1) x‖ ≤ a n := by
  rw [norm_mul, Real.norm_of_nonneg (ha0 n)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (norm_fourierTiltSlope_succ_le_one n x) (ha0 n)

lemma norm_weighted_fourierCurvature_le (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (n : ℕ) (x : ℝ) :
    ‖a n * (2 * Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x))‖ ≤ a n * 2 := by
  rw [norm_mul, Real.norm_of_nonneg (ha0 n), norm_mul]
  rw [show ‖(2 : ℝ)‖ = 2 by norm_num]
  have hc : ‖Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x)‖ ≤ 1 :=
    Real.abs_cos_le_one _
  calc
    _ ≤ a n * (2 * 1) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hc (by norm_num)) (ha0 n)
    _ = _ := by ring

theorem hasDerivAt_fourierMixtureShape (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) (x : ℝ) :
    HasDerivAt (fourierMixtureShape a) (fourierMixtureSlope a x) x := by
  apply hasDerivAt_tsum ha
    (fun n y => (hasDerivAt_fourierTiltShape (n + 1) (Nat.succ_pos _) y).const_mul (a n))
    (fun n y => norm_weighted_fourierTiltSlope_le a ha0 n y)
    (y₀ := 0)
  simp [fourierTiltShape]

theorem hasDerivAt_fourierMixtureSlope (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) (x : ℝ) :
    HasDerivAt (fourierMixtureSlope a) (fourierMixtureCurvature a x) x := by
  apply hasDerivAt_tsum (ha.mul_right 2)
    (fun n y => (hasDerivAt_fourierTiltSlope (n + 1) (Nat.succ_pos _) y).const_mul (a n))
    (fun n y => norm_weighted_fourierCurvature_le a ha0 n y)
    (y₀ := 0)
  simp [fourierTiltSlope]

theorem iteratedDeriv_two_fourierMixtureShape (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) (x : ℝ) :
    iteratedDeriv 2 (fourierMixtureShape a) x = fourierMixtureCurvature a x := by
  have hfirst : deriv (fourierMixtureShape a) = fourierMixtureSlope a := by
    funext y
    exact (hasDerivAt_fourierMixtureShape a ha0 ha y).deriv
  rw [iteratedDeriv_eq_iterate]
  change deriv (deriv (fourierMixtureShape a)) x = _
  rw [hfirst]
  exact (hasDerivAt_fourierMixtureSlope a ha0 ha x).deriv

theorem continuous_fourierMixtureCurvature (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) :
    Continuous (fourierMixtureCurvature a) := by
  apply continuous_tsum (fun n => by fun_prop) (ha.mul_right 2)
  exact fun n x => norm_weighted_fourierCurvature_le a ha0 n x

end
end CGLMPBounds.Partition
