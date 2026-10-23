module

public import CGLMPBounds.Hardy.PolynomialSegmentIntegration
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section


/-! Actual disjoint two-node circle integrals of a polynomial numerator.
The recurrence is a pointwise rational identity; the single-node boundary
values follow from Cauchy's derivative formula and a zero integral on the
other disk. These provide the contour half of the C.10 beta comparison. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Complex Metric Set
open scoped Polynomial

/-- An explicit sum of two circle integrals, retaining both pole clusters. -/
def polynomialTwoCircleIntegral (f : ℂ[X]) (a b : ℂ) (p q : ℕ) : ℂ :=
  let R := ‖a - b‖ / 3
  ((∮ z in C(a, R), f.eval z / ((z - a) ^ p * (z - b) ^ q)) +
    (∮ z in C(b, R), f.eval z / ((z - a) ^ p * (z - b) ^ q))) /
      (2 * Real.pi * Complex.I : ℂ)

lemma twoCircle_radius_pos {a b : ℂ} (hab : a ≠ b) : 0 < ‖a - b‖ / 3 :=
  div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab)) (by norm_num)

lemma twoCircle_closedBall_ne_other {a b z : ℂ} (hab : a ≠ b)
    (hz : z ∈ closedBall a (‖a - b‖ / 3)) : z ≠ b := by
  intro heq
  subst z
  have hd : dist b a = ‖a - b‖ := by rw [dist_comm, dist_eq_norm]
  have h := Metric.mem_closedBall.mp hz
  rw [hd] at h
  have hp := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  linarith

lemma twoCircle_sphere_ne_left {a b z : ℂ} (hab : a ≠ b)
    (hz : z ∈ sphere a (‖a - b‖ / 3)) : z ≠ a := by
  intro heq
  subst z
  have h := Metric.mem_sphere.mp hz
  simp only [dist_self] at h
  linarith [twoCircle_radius_pos hab]

lemma polynomial_twoCircle_circleIntegrable (f : ℂ[X]) {a b : ℂ}
    (hab : a ≠ b) (p q : ℕ) :
    CircleIntegrable (fun z => f.eval z / ((z - a) ^ p * (z - b) ^ q))
      a (‖a - b‖ / 3) := by
  apply ContinuousOn.circleIntegrable (twoCircle_radius_pos hab).le
  apply f.differentiable.continuous.continuousOn.div
    (((continuousOn_id.sub continuousOn_const).pow p).mul
      ((continuousOn_id.sub continuousOn_const).pow q))
  intro z hz
  exact mul_ne_zero
    (pow_ne_zero _ (sub_ne_zero.mpr (twoCircle_sphere_ne_left hab hz)))
    (pow_ne_zero _ (sub_ne_zero.mpr
      (twoCircle_closedBall_ne_other hab (sphere_subset_closedBall hz))))

lemma polynomial_twoCircle_circleIntegrable_right (f : ℂ[X]) {a b : ℂ}
    (hab : a ≠ b) (p q : ℕ) :
    CircleIntegrable (fun z => f.eval z / ((z - a) ^ p * (z - b) ^ q))
      b (‖a - b‖ / 3) := by
  simpa only [norm_sub_rev, mul_comm] using
    polynomial_twoCircle_circleIntegrable f hab.symm q p

lemma iteratedDeriv_polynomial_eval (f : ℂ[X]) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w => f.eval w) z = ((Polynomial.derivative^[n]) f).eval z := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    have hderiv : deriv (fun w : ℂ => f.eval w) = fun w => f.derivative.eval w :=
      funext fun w => f.deriv
    rw [iteratedDeriv_succ', hderiv, ih, Function.iterate_succ_apply]

lemma polynomial_circle_integral_single_pole (f : ℂ[X]) (a : ℂ)
    {R : ℝ} (hR : 0 < R) (n : ℕ) :
    (∮ z in C(a, R), f.eval z / (z - a) ^ (n + 1)) =
      (2 * Real.pi * Complex.I : ℂ) *
        (((Polynomial.derivative^[n]) f).eval a / (n.factorial : ℂ)) := by
  have h := DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul hR n
    (f.differentiable.differentiableOn : DifferentiableOn ℂ (fun z => f.eval z) (closedBall a R))
  simp only [smul_eq_mul, one_div, iteratedDeriv_polynomial_eval] at h
  convert h using 1
  · congr 1
    funext z
    ring
  · ring

lemma polynomial_circle_integral_other_pole (f : ℂ[X]) {a b : ℂ}
    (hab : a ≠ b) (n : ℕ) :
    (∮ z in C(a, ‖a - b‖ / 3), f.eval z / (z - b) ^ n) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (twoCircle_radius_pos hab).le (s := (∅ : Set ℂ)) Set.countable_empty
  · exact f.differentiable.continuous.continuousOn.div
      ((continuousOn_id.sub continuousOn_const).pow n)
      (fun z hz => pow_ne_zero _ (sub_ne_zero.mpr (twoCircle_closedBall_ne_other hab hz)))
  · intro z hz
    exact f.differentiableAt.div ((differentiableAt_id.sub_const b).pow n)
      (pow_ne_zero _ (sub_ne_zero.mpr
        (twoCircle_closedBall_ne_other hab (ball_subset_closedBall hz.1))))

lemma polynomialTwoCircleIntegral_left_axis (f : ℂ[X]) {a b : ℂ}
    (hab : a ≠ b) (n : ℕ) :
    polynomialTwoCircleIntegral f a b (n + 1) 0 =
      ((Polynomial.derivative^[n]) f).eval a / (n.factorial : ℂ) := by
  unfold polynomialTwoCircleIntegral
  simp only [pow_zero, mul_one]
  rw [polynomial_circle_integral_single_pole f a (twoCircle_radius_pos hab) n,
    show (∮ z in C(b, ‖a - b‖ / 3), f.eval z / (z - a) ^ (n + 1)) = 0 by
      simpa only [norm_sub_rev] using polynomial_circle_integral_other_pole f hab.symm (n + 1),
    add_zero, mul_div_cancel_left₀ _ Complex.two_pi_I_ne_zero]

lemma polynomialTwoCircleIntegral_swap (f : ℂ[X]) (a b : ℂ) (p q : ℕ) :
    polynomialTwoCircleIntegral f a b p q = polynomialTwoCircleIntegral f b a q p := by
  unfold polynomialTwoCircleIntegral
  simp only [norm_sub_rev, mul_comm, add_comm]

lemma polynomialTwoCircleIntegral_right_axis (f : ℂ[X]) {a b : ℂ}
    (hab : a ≠ b) (n : ℕ) :
    polynomialTwoCircleIntegral f a b 0 (n + 1) =
      ((Polynomial.derivative^[n]) f).eval b / (n.factorial : ℂ) := by
  rw [polynomialTwoCircleIntegral_swap]
  exact polynomialTwoCircleIntegral_left_axis f hab.symm n

lemma polynomialTwoCircleIntegral_recurrence (f : ℂ[X]) {a b : ℂ}
    (hab : a ≠ b) (p q : ℕ) :
    (a - b) * polynomialTwoCircleIntegral f a b (p + 1) (q + 1) =
      polynomialTwoCircleIntegral f a b (p + 1) q -
        polynomialTwoCircleIntegral f a b p (q + 1) := by
  let F := fun p q : ℕ => fun z : ℂ => f.eval z / ((z - a) ^ p * (z - b) ^ q)
  have hpoint {z : ℂ} (ha : z ≠ a) (hb : z ≠ b) :
      (a - b) * F (p + 1) (q + 1) z = F (p + 1) q z - F p (q + 1) z := by
    dsimp only [F]
    simp only [pow_succ]
    field_simp [sub_ne_zero.mpr ha, sub_ne_zero.mpr hb]
    <;> ring
  have hcircle (c : ℂ)
      (hsep : ∀ z ∈ sphere c (‖a - b‖ / 3), z ≠ a ∧ z ≠ b)
      (h₁ : CircleIntegrable (F (p + 1) q) c (‖a - b‖ / 3))
      (h₂ : CircleIntegrable (F p (q + 1)) c (‖a - b‖ / 3)) :
      (a - b) * (∮ z in C(c, ‖a - b‖ / 3), F (p + 1) (q + 1) z) =
        (∮ z in C(c, ‖a - b‖ / 3), F (p + 1) q z) -
          (∮ z in C(c, ‖a - b‖ / 3), F p (q + 1) z) := by
    rw [← circleIntegral.integral_const_mul, ← circleIntegral.integral_sub h₁ h₂]
    exact circleIntegral.integral_congr (twoCircle_radius_pos hab).le
      (fun z hz => hpoint (hsep z hz).1 (hsep z hz).2)
  have hleft := hcircle a
    (fun z hz => ⟨twoCircle_sphere_ne_left hab hz,
      twoCircle_closedBall_ne_other hab (sphere_subset_closedBall hz)⟩)
    (polynomial_twoCircle_circleIntegrable f hab (p + 1) q)
    (polynomial_twoCircle_circleIntegrable f hab p (q + 1))
  have hright := hcircle b (by
      intro z hz
      have hz' : z ∈ sphere b (‖b - a‖ / 3) := by simpa only [norm_sub_rev] using hz
      exact ⟨twoCircle_closedBall_ne_other hab.symm (sphere_subset_closedBall hz'),
        twoCircle_sphere_ne_left hab.symm hz'⟩)
    (polynomial_twoCircle_circleIntegrable_right f hab (p + 1) q)
    (polynomial_twoCircle_circleIntegrable_right f hab p (q + 1))
  unfold polynomialTwoCircleIntegral
  change (a - b) * ((_ + _) / _) = (_ + _) / _ - (_ + _) / _
  dsimp only [F] at hleft hright
  linear_combination (hleft + hright) / (2 * Real.pi * Complex.I : ℂ)

end
end CGLMPBounds.Hardy
