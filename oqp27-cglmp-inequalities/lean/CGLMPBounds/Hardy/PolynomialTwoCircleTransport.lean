module

public import CGLMPBounds.Hardy.PolynomialTwoNodeBeta
public import CGLMPBounds.Hardy.SchwarzPartialFractions
public import CGLMPBounds.Hardy.SchwarzFinitePoleIntegral

@[expose] public section


/-! Genuine transport of a polynomial two-node rational integral from any
circle enclosing both nodes to the two disjoint explicit small circles.
The partial fractions are constructed once, for this actual numerator and
denominator, and each pole is assigned to its actual small disk. -/

open scoped Polynomial

namespace CGLMPBounds.Hardy
noncomputable section
open Complex Metric Set

theorem polynomial_circleIntegral_eq_twoCircleIntegral (f : ℂ[X]) {a b c : ℂ}
    (hab : a ≠ b) (p q : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (ha : a ∈ ball c R) (hb : b ∈ ball c R) :
    (∮ z in C(c, R), f.eval z / ((z - a) ^ p * (z - b) ^ q)) /
        (2 * Real.pi * Complex.I : ℂ) =
      polynomialTwoCircleIntegral f a b p q := by
  classical
  let S : ℝ := ‖a - b‖ / 3
  have hS : 0 < S := twoCircle_radius_pos hab
  have haa : a ∈ ball a S := by simpa only [mem_ball, dist_self] using hS
  have hbb : b ∈ ball b S := by simpa only [mem_ball, dist_self] using hS
  have hba : b ∉ closedBall a S := by
    intro h
    exact twoCircle_closedBall_ne_other hab h rfl
  have hab' : a ∉ closedBall b S := by
    intro h
    have h' : a ∈ closedBall b (‖b - a‖ / 3) := by
      simpa only [norm_sub_rev] using h
    exact twoCircle_closedBall_ne_other hab.symm h' rfl
  have hnoaa : a ∉ sphere a S := by
    intro h
    exact (ne_of_lt (Metric.mem_ball.mp haa)) (Metric.mem_sphere.mp h)
  have hnobb : b ∉ sphere b S := by
    intro h
    exact (ne_of_lt (Metric.mem_ball.mp hbb)) (Metric.mem_sphere.mp h)
  have hnoac : a ∉ sphere c R := by
    intro h
    exact (ne_of_lt (Metric.mem_ball.mp ha)) (Metric.mem_sphere.mp h)
  have hnobc : b ∉ sphere c R := by
    intro h
    exact (ne_of_lt (Metric.mem_ball.mp hb)) (Metric.mem_sphere.mp h)
  have hnotab : a ∉ ball b S := fun h => hab' (ball_subset_closedBall h)
  have hnotba : b ∉ ball a S := fun h => hba (ball_subset_closedBall h)
  let nodes : Finset ℂ := {a, b}
  let order : ℂ → ℕ := fun v => if v = a then p else q
  obtain ⟨Q, d, hd⟩ := exists_complex_partial_fractions f nodes order
  let κ := Σ v : nodes, Fin (order v.val)
  let pole : κ → ℂ := fun i => i.1.val
  let coeff : κ → ℂ := fun i => d i.1.val i.2
  let power : κ → ℕ := fun i => i.2.val + 1
  let F : ℂ → ℂ := fun z => Q.eval z + ∑ i : κ, coeff i * (z - pole i)⁻¹ ^ power i
  have hpole (i : κ) : pole i = a ∨ pole i = b := by
    simpa only [pole, nodes, Finset.mem_insert, Finset.mem_singleton] using i.1.property
  have heq (z : ℂ) (hza : z ≠ a) (hzb : z ≠ b) :
      f.eval z / ((z - a) ^ p * (z - b) ^ q) = F z := by
    have hz : z ∉ nodes := by simp only [nodes, Finset.mem_insert,
      Finset.mem_singleton, not_or, hza, hzb, not_false_eq_true, and_self]
    calc
      _ = f.eval z * ∏ v ∈ nodes, (z - v)⁻¹ ^ order v := by
        simp [nodes, order, hab, hab.symm, div_eq_mul_inv, inv_pow,
          mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
      _ = F z := by
        rw [hd z hz]
        change Q.eval z + (∑ v ∈ nodes, ∑ j : Fin (order v),
          d v j * (z - v)⁻¹ ^ (j.val + 1)) =
          Q.eval z + ∑ i : (Σ v : nodes, Fin (order v.val)),
            d i.1.val i.2 * (z - i.1.val)⁻¹ ^ (i.2.val + 1)
        rw [Fintype.sum_sigma]
        exact congrArg (fun w : ℂ => Q.eval z + w)
          (Finset.sum_coe_sort (s := nodes)
            (f := fun v : ℂ => ∑ j : Fin (order v),
              d v j * (z - v)⁻¹ ^ (j.val + 1))).symm
  have hsep (d : ℂ) (T : ℝ) (ha' : a ∉ sphere d T) (hb' : b ∉ sphere d T) :
      ∀ i ∈ (Finset.univ : Finset κ), pole i ∉ sphere d T := by
    intro i _
    rcases hpole i with h | h
    · simpa only [h] using ha'
    · simpa only [h] using hb'
  have htransport := circleIntegral_finite_poles_partition Finset.univ Q pole coeff power
    hS.le hS.le hR
    (hsep a S hnoaa (fun h => hba (sphere_subset_closedBall h)))
    (hsep b S (fun h => hab' (sphere_subset_closedBall h)) hnobb)
    (hsep c R hnoac hnobc)
    (by
      intro i _
      rcases hpole i with h | h
      · simpa only [h] using ha
      · simpa only [h] using hb)
    (by
      intro i _
      rcases hpole i with h | h
      · simp only [h, haa, hnotab, not_false_eq_true]
      · simp only [h, hnotba, hbb, not_true_eq_false])
  have hcircle (d : ℂ) (T : ℝ) (hT : 0 ≤ T)
      (ha' : a ∉ sphere d T) (hb' : b ∉ sphere d T) :
      (∮ z in C(d, T), f.eval z / ((z - a) ^ p * (z - b) ^ q)) =
        ∮ z in C(d, T), F z := by
    apply circleIntegral.integral_congr hT
    intro z hz
    exact heq z (fun h => ha' (h ▸ hz)) (fun h => hb' (h ▸ hz))
  dsimp only [polynomialTwoCircleIntegral]
  rw [hcircle c R hR hnoac hnobc,
    hcircle a S hS.le hnoaa (fun h => hba (sphere_subset_closedBall h)),
    hcircle b S hS.le (fun h => hab' (sphere_subset_closedBall h)) hnobb]
  exact congrArg (fun z : ℂ => z / (2 * Real.pi * Complex.I : ℂ)) htransport.symm

/-- The actual outer-circle integral is the actual weighted segment integral.
The two positive denominator orders ensure that both nodes occur. -/
theorem polynomial_circleIntegral_eq_beta (f : ℂ[X]) {a b c : ℂ}
    (hab : a ≠ b) (p q : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (ha : a ∈ ball c R) (hb : b ∈ ball c R) :
    (∮ z in C(c, R), f.eval z / ((z - a) ^ (p + 1) * (z - b) ^ (q + 1))) /
        (2 * Real.pi * Complex.I : ℂ) =
      polynomialBetaDividedDifference f a b p q := by
  rw [polynomial_circleIntegral_eq_twoCircleIntegral f hab (p + 1) (q + 1) hR ha hb,
    polynomialTwoCircleIntegral_eq_beta f hab p q]

end
end CGLMPBounds.Hardy
