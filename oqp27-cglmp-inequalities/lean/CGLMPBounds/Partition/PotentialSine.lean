module

public import Mathlib

@[expose] public section


/-! The explicit positive fourth derivative of the negative u*sin(a*u)
term in the source's shifted D.5 potential. -/

namespace CGLMPBounds.Partition
noncomputable section

private lemma hasDerivAt_sin_mul (a x : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin (a * u)) (a * Real.cos (a * x)) x := by
  convert ((hasDerivAt_id' x).const_mul a).sin using 1 <;> (try funext u) <;> (try dsimp) <;> ring

private lemma hasDerivAt_cos_mul (a x : ℝ) :
    HasDerivAt (fun u : ℝ => Real.cos (a * u)) (-a * Real.sin (a * x)) x := by
  convert ((hasDerivAt_id' x).const_mul a).cos using 1 <;> (try funext u) <;> (try dsimp) <;> ring

private lemma deriv_negative_sine_moment (a x : ℝ) :
    deriv (fun u : ℝ => -u * Real.sin (a * u)) x =
      -Real.sin (a * x) - a * x * Real.cos (a * x) := by
  have h := ((hasDerivAt_id' x).mul (hasDerivAt_sin_mul a x)).neg
  have hh : HasDerivAt (fun u : ℝ => -u * Real.sin (a * u))
      (-Real.sin (a * x) - a * x * Real.cos (a * x)) x := by
    convert h using 1 <;> (try funext u) <;> (try dsimp) <;> ring
  exact hh.deriv

private lemma deriv_negative_sine_moment_first (a x : ℝ) :
    deriv (fun u : ℝ => -Real.sin (a * u) - a * u * Real.cos (a * u)) x =
      -2 * a * Real.cos (a * x) + a ^ 2 * x * Real.sin (a * x) := by
  have h := (hasDerivAt_sin_mul a x).neg.sub
    (((hasDerivAt_id' x).const_mul a).mul (hasDerivAt_cos_mul a x))
  have hh : HasDerivAt
      (fun u : ℝ => -Real.sin (a * u) - a * u * Real.cos (a * u))
      (-2 * a * Real.cos (a * x) + a ^ 2 * x * Real.sin (a * x)) x := by
    convert h using 1 <;> (try funext u) <;> (try dsimp) <;> ring
  exact hh.deriv

private lemma deriv_negative_sine_moment_second (a x : ℝ) :
    deriv (fun u : ℝ => -2 * a * Real.cos (a * u) + a ^ 2 * u * Real.sin (a * u)) x =
      3 * a ^ 2 * Real.sin (a * x) + a ^ 3 * x * Real.cos (a * x) := by
  have h := ((hasDerivAt_cos_mul a x).const_mul (-2 * a)).add
    (((hasDerivAt_id' x).const_mul (a ^ 2)).mul (hasDerivAt_sin_mul a x))
  have hh : HasDerivAt
      (fun u : ℝ => -2 * a * Real.cos (a * u) + a ^ 2 * u * Real.sin (a * u))
      (3 * a ^ 2 * Real.sin (a * x) + a ^ 3 * x * Real.cos (a * x)) x := by
    convert h using 1 <;> (try funext u) <;> (try dsimp) <;> ring
  exact hh.deriv

private lemma deriv_negative_sine_moment_third (a x : ℝ) :
    deriv (fun u : ℝ => 3 * a ^ 2 * Real.sin (a * u) + a ^ 3 * u * Real.cos (a * u)) x =
      a ^ 3 * (4 * Real.cos (a * x) - a * x * Real.sin (a * x)) := by
  have h := ((hasDerivAt_sin_mul a x).const_mul (3 * a ^ 2)).add
    (((hasDerivAt_id' x).const_mul (a ^ 3)).mul (hasDerivAt_cos_mul a x))
  have hh : HasDerivAt
      (fun u : ℝ => 3 * a ^ 2 * Real.sin (a * u) + a ^ 3 * u * Real.cos (a * u))
      (a ^ 3 * (4 * Real.cos (a * x) - a * x * Real.sin (a * x))) x := by
    convert h using 1 <;> (try funext u) <;> (try dsimp) <;> ring
  exact hh.deriv

theorem iteratedDeriv_four_negative_sine_moment (a x : ℝ) :
    iteratedDeriv 4 (fun u : ℝ => -u * Real.sin (a * u)) x =
      a ^ 3 * (4 * Real.cos (a * x) - a * x * Real.sin (a * x)) := by
  rw [iteratedDeriv_eq_iterate]
  change deriv (fun u : ℝ => deriv (fun v : ℝ => deriv (fun w : ℝ =>
    deriv (fun t : ℝ => -t * Real.sin (a * t)) w) v) u) x = _
  simp only [deriv_negative_sine_moment, deriv_negative_sine_moment_first,
    deriv_negative_sine_moment_second, deriv_negative_sine_moment_third]

lemma four_cos_sub_mul_sin_pos {t : ℝ} (ht : |t| ≤ 1) :
    0 < 4 * Real.cos t - t * Real.sin t := by
  have hsq : t ^ 2 ≤ 1 := by
    have ht' := abs_le.mp ht
    nlinarith [ht'.1, ht'.2]
  have hprod : |t * Real.sin t| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using
      mul_le_mul ht (Real.abs_sin_le_one t) (abs_nonneg _) zero_le_one
  have hprod' : t * Real.sin t ≤ 1 := (le_abs_self _).trans hprod
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]

theorem iteratedDeriv_four_negative_sine_moment_pos
    {a x : ℝ} (ha : 0 < a) (hx : |a * x| ≤ 1) :
    0 < iteratedDeriv 4 (fun u : ℝ => -u * Real.sin (a * u)) x := by
  rw [iteratedDeriv_four_negative_sine_moment]
  exact mul_pos (pow_pos ha _) (four_cos_sub_mul_sin_pos hx)

theorem source_negative_sine_moment_fourth_pos {u : ℝ} (hu : |u| ≤ 1 / 2) :
    0 < iteratedDeriv 4 (fun t : ℝ => -t * Real.sin ((Real.pi / 2) * t)) u := by
  apply iteratedDeriv_four_negative_sine_moment_pos (by positivity)
  rw [abs_mul, abs_of_pos (show 0 < Real.pi / 2 by positivity)]
  have h := mul_le_mul_of_nonneg_left hu (show 0 ≤ Real.pi / 2 by positivity)
  nlinarith [Real.pi_lt_four]

end
end CGLMPBounds.Partition
