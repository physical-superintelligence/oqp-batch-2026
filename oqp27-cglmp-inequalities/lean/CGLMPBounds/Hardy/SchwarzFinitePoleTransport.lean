module

public import CGLMPBounds.Hardy.SchwarzInversionResidues
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section


/-! Actual linear extension of inversion transport from rational basis
functions to a polynomial plus finitely many poles. Every summand is proved
circle integrable from the explicit pole separation; linearity never relies
on a totalized undefined integral. -/

open Complex Metric Set Polynomial

namespace CGLMPBounds.Hardy
noncomputable section

lemma circleIntegral_polynomial_eq_zero (q : ℂ[X]) {c : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    (∮ z in C(c, R), q.eval z) = 0 := by
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR
    (s := (∅ : Set ℂ)) Set.countable_empty q.continuousOn (fun z _ => q.differentiableAt)

lemma circleIntegral_inverse_pullback_polynomial_eq_zero (q : ℂ[X])
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hzero : (0 : ℂ) ∉ closedBall c R) :
    (∮ z in C(c, R), -(z ^ 2)⁻¹ * q.eval z⁻¹) = 0 := by
  have hz : ∀ z ∈ closedBall c R, z ≠ 0 := fun z hzc he => hzero (he ▸ hzc)
  have hi : ContinuousOn (fun z : ℂ => z⁻¹) (closedBall c R) :=
    continuousOn_id.inv₀ hz
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR
    (s := (∅ : Set ℂ)) Set.countable_empty
  · exact ((continuousOn_id.pow 2).inv₀ (fun z hzc => pow_ne_zero _ (hz z hzc))).neg.mul
      (q.continuous.comp_continuousOn hi)
  · intro z hzc
    have hzn := hz z (ball_subset_closedBall hzc.1)
    exact (((differentiableAt_id.pow 2).inv (pow_ne_zero _ hzn)).neg).mul
      (q.differentiableAt.comp z ((hasDerivAt_inv hzn).differentiableAt))

lemma inverse_pullback_power_continuousOn {a c : ℂ} {R : ℝ}
    (hzero : (0 : ℂ) ∉ closedBall c R) (hsep : a⁻¹ ∉ sphere c R) (k : ℕ) :
    ContinuousOn (fun z : ℂ => -(z ^ 2)⁻¹ * (z⁻¹ - a)⁻¹ ^ k) (sphere c R) := by
  have hz : ∀ z ∈ sphere c R, z ≠ 0 :=
    fun z hzc he => hzero (he ▸ sphere_subset_closedBall hzc)
  have hi : ContinuousOn (fun z : ℂ => z⁻¹) (sphere c R) :=
    continuousOn_id.inv₀ hz
  have hza : ∀ z ∈ sphere c R, z⁻¹ - a ≠ 0 := by
    intro z hzc he
    apply hsep
    have heq : z = a⁻¹ := by rw [← sub_eq_zero.mp he, inv_inv]
    exact heq ▸ hzc
  exact ((continuousOn_id.pow 2).inv₀ (fun z hzc => pow_ne_zero _ (hz z hzc))).neg.mul
    (((hi.sub continuousOn_const).inv₀ hza).pow k)

lemma power_pole_continuousOn {a d : ℂ} {S : ℝ}
    (hsep : a ∉ sphere d S) (k : ℕ) :
    ContinuousOn (fun z : ℂ => (z - a)⁻¹ ^ k) (sphere d S) :=
  (((continuousOn_id.sub continuousOn_const).inv₀
    (fun z hzc => sub_ne_zero.mpr (ne_of_mem_of_not_mem hzc hsep))).pow k)

/-- Finite-pole transport, with actual summand integrability and no integral
identity among the hypotheses. The same pole may occur repeatedly. -/
theorem circleIntegral_inverse_pullback_finite_poles {κ : Type*}
    (s : Finset κ) (q : ℂ[X]) (a b : κ → ℂ) (k : κ → ℕ)
    {c d : ℂ} {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hzero : (0 : ℂ) ∉ closedBall c R)
    (ha : ∀ i ∈ s, a i ≠ 0)
    (hsrc : ∀ i ∈ s, (a i)⁻¹ ∉ sphere c R)
    (htgt : ∀ i ∈ s, a i ∉ sphere d S)
    (hselect : ∀ i ∈ s, (a i)⁻¹ ∈ ball c R ↔ a i ∈ ball d S) :
    (∮ z in C(c, R), -(z ^ 2)⁻¹ *
      (q.eval z⁻¹ + ∑ i ∈ s, b i * (z⁻¹ - a i)⁻¹ ^ k i)) =
      ∮ z in C(d, S), q.eval z + ∑ i ∈ s, b i * (z - a i)⁻¹ ^ k i := by
  classical
  have hpoly : CircleIntegrable (fun z : ℂ => -(z ^ 2)⁻¹ * q.eval z⁻¹) c R := by
    have hz : ∀ z ∈ sphere c R, z ≠ 0 :=
      fun z hzc he => hzero (he ▸ sphere_subset_closedBall hzc)
    exact (((continuousOn_id.pow 2).inv₀
      (fun z hzc => pow_ne_zero _ (hz z hzc))).neg.mul
        (q.continuous.comp_continuousOn (continuousOn_id.inv₀ hz))).circleIntegrable hR
  have hsrcI : ∀ i ∈ s, CircleIntegrable
      (fun z : ℂ => b i * (-(z ^ 2)⁻¹ * (z⁻¹ - a i)⁻¹ ^ k i)) c R := by
    intro i hi
    exact (continuousOn_const.mul
      (inverse_pullback_power_continuousOn hzero (hsrc i hi) (k i))).circleIntegrable hR
  have htgtI : ∀ i ∈ s, CircleIntegrable
      (fun z : ℂ => b i * (z - a i)⁻¹ ^ k i) d S := by
    intro i hi
    exact (continuousOn_const.mul (power_pole_continuousOn (htgt i hi) (k i))).circleIntegrable hS
  have hsrcsum : CircleIntegrable
      (fun z : ℂ => ∑ i ∈ s, b i * (-(z ^ 2)⁻¹ * (z⁻¹ - a i)⁻¹ ^ k i)) c R := by
    convert! CircleIntegrable.sum s hsrcI using 1
    funext z
    simp only [Finset.sum_apply]
  have htgtsum : CircleIntegrable
      (fun z : ℂ => ∑ i ∈ s, b i * (z - a i)⁻¹ ^ k i) d S := by
    convert! CircleIntegrable.sum s htgtI using 1
    funext z
    simp only [Finset.sum_apply]
  have hfun : (fun z : ℂ => -(z ^ 2)⁻¹ *
      (q.eval z⁻¹ + ∑ i ∈ s, b i * (z⁻¹ - a i)⁻¹ ^ k i)) =
      (fun z : ℂ => -(z ^ 2)⁻¹ * q.eval z⁻¹ +
        ∑ i ∈ s, b i * (-(z ^ 2)⁻¹ * (z⁻¹ - a i)⁻¹ ^ k i)) := by
    funext z
    simp only [mul_add, Finset.mul_sum, mul_left_comm (-(z ^ 2)⁻¹)]
  rw [hfun, circleIntegral.integral_add hpoly hsrcsum,
    circleIntegral.integral_add (q.continuousOn.circleIntegrable hS) htgtsum,
    circleIntegral_inverse_pullback_polynomial_eq_zero q hR hzero,
    circleIntegral_polynomial_eq_zero q hS, zero_add, zero_add,
    circleIntegral.integral_fun_sum hsrcI, circleIntegral.integral_fun_sum htgtI]
  apply Finset.sum_congr rfl
  intro i hi
  rw [circleIntegral.integral_const_mul, circleIntegral.integral_const_mul]
  congr 1
  simpa only [zpow_neg, zpow_natCast, inv_pow] using
    circleIntegral_inverse_pullback_power_basis (-(k i : ℤ)) (ha i hi) hR hS hzero
      (hsrc i hi) (htgt i hi) (hselect i hi)

end
end CGLMPBounds.Hardy
