module

public import CGLMPBounds.Hardy.TwoNodeResidue

@[expose] public section


/-! The unmixed cycles omitted from C.13 have actual zero contour integrals.
These are analytic cancellation theorems, not a convention in the residue. -/

open Complex Metric Set
namespace CGLMPBounds.Hardy
noncomputable section

theorem twoNodeResidue_zero_left (q : ℕ) {a b : ℝ} (hab : a ≠ b) :
    twoNodeResidue 0 q a b = 0 := by
  have hf : ∀ z ∈ closedBall (a : ℂ) (|a - b| / 2),
      DifferentiableAt ℂ (fun w : ℂ => w ^ (q - 2) / (w - (b : ℂ)) ^ q) z := by
    intro z hz
    exact (differentiableAt_id.pow _).div
      ((differentiableAt_id.sub_const _).pow _)
      (pow_ne_zero _ (sub_ne_zero.mpr (twoNode_closedBall_ne_right hab hz)))
  have hc : ContinuousOn (fun w : ℂ => w ^ (q - 2) / (w - (b : ℂ)) ^ q)
      (closedBall (a : ℂ) (|a - b| / 2)) :=
    fun z hz => (hf z hz).continuousAt.continuousWithinAt
  have hi := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (twoNode_radius_pos hab).le (s := (∅ : Set ℂ)) Set.countable_empty hc
    (fun z hz => hf z (ball_subset_closedBall hz.1))
  simpa only [twoNodeResidue, zero_add, pow_zero, one_mul, hi, zero_div] using
    (show (0 : ℂ) = 0 from rfl)

theorem twoNodeResidue_zero_right (p : ℕ) (hp : 2 ≤ p) {a b : ℝ} (hab : a ≠ b) :
    twoNodeResidue p 0 a b = 0 := by
  have hC := DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul
    (twoNode_radius_pos hab) (p - 1)
    (show DifferentiableOn ℂ (fun z : ℂ => z ^ (p - 2))
      (closedBall (a : ℂ) (|a - b| / 2)) from (differentiable_pow _).differentiableOn)
  have hder : iteratedDeriv (p - 1) (fun z : ℂ => z ^ (p - 2)) (a : ℂ) = 0 := by
    rw [iteratedDeriv_pow, Nat.descFactorial_of_lt (by omega), Nat.cast_zero, zero_mul]
  rw [hder, smul_zero] at hC
  have hfun : (fun z : ℂ => (1 / (z - (a : ℂ)) ^ (p - 1 + 1)) • z ^ (p - 2)) =
      (fun z : ℂ => z ^ (p - 2) / (z - (a : ℂ)) ^ p) := by
    funext z
    rw [show p - 1 + 1 = p by omega, smul_eq_mul]
    ring
  rw [hfun] at hC
  simpa only [twoNodeResidue, add_zero, pow_zero, mul_one, hC, zero_div] using
    (show (0 : ℂ) = 0 from rfl)

theorem twoNode_rational_circleIntegrable (p q : ℕ) {a b : ℝ} (hab : a ≠ b) :
    CircleIntegrable (fun z : ℂ => z ^ (p + q - 2) /
      ((z - (a : ℂ)) ^ p * (z - (b : ℂ)) ^ q)) (a : ℂ) (|a - b| / 2) := by
  apply ContinuousOn.circleIntegrable (twoNode_radius_pos hab).le
  apply (continuousOn_id.pow _).div
    (((continuousOn_id.sub continuousOn_const).pow _).mul
      ((continuousOn_id.sub continuousOn_const).pow _))
  intro z hz
  have hza : z ≠ (a : ℂ) := by
    intro heq
    subst z
    have he := Metric.mem_sphere.mp hz
    simp only [dist_self] at he
    exact (ne_of_gt (twoNode_radius_pos hab)) he.symm
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hza))
    (pow_ne_zero _ (sub_ne_zero.mpr (twoNode_closedBall_ne_right hab
      (sphere_subset_closedBall hz))))

end
end CGLMPBounds.Hardy
