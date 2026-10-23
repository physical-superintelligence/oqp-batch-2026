module

public import CGLMPBounds.Hardy.SchwarzCirclePowerTrace
public import Mathlib.Analysis.Calculus.Deriv.ZPow

@[expose] public section


/-! Actual residue transport for every partial-fraction basis under ζ↦ζ⁻¹.
Non-simple poles are handled by a genuine differentiated primitive, so
multiplicities are not restricted. The simple-pole pullback is the exact
difference of two inverse kernels; the zero kernel vanishes because the
source disk avoids zero. This is analytic infrastructure for C.7, not a
substitute assumption of contour inversion for the matrix integrand. -/

open Complex Metric Set
open scoped Topology Classical

namespace CGLMPBounds.Hardy
noncomputable section

lemma circleIntegral_inverse_pullback_zpow_of_ne {n : ℤ} (hn : n ≠ -1)
    {a c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ z ∈ sphere c R, z ≠ 0)
    (ha : ∀ z ∈ sphere c R, z⁻¹ ≠ a) :
    (∮ z in C(c, R), -(z ^ 2)⁻¹ * (z⁻¹ - a) ^ n) = 0 := by
  apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR
    (f := fun z => (z⁻¹ - a) ^ (n + 1) / ((n : ℂ) + 1))
  intro z hzc
  have hnn : (n : ℂ) + 1 ≠ 0 := by
    rw [← Int.cast_one, ← Int.cast_add, Int.cast_ne_zero]
    omega
  have hu := (hasDerivAt_inv (hz z hzc)).sub_const a
  have hd := ((hasDerivAt_zpow (n + 1) (z⁻¹ - a)
    (Or.inl (sub_ne_zero.mpr (ha z hzc)))).comp z hu).div_const ((n : ℂ) + 1)
  have hd' : HasDerivAt (fun z => (z⁻¹ - a) ^ (n + 1) / ((n : ℂ) + 1))
      (-(z ^ 2)⁻¹ * (z⁻¹ - a) ^ n) z := by
    have hcoeff : ((n + 1 : ℤ) : ℂ) * (z⁻¹ - a) ^ (n + 1 - 1) *
        -(z ^ 2)⁻¹ / ((n : ℂ) + 1) = -(z ^ 2)⁻¹ * (z⁻¹ - a) ^ n := by
      simp only [add_sub_cancel, Int.cast_add, Int.cast_one]
      field_simp [hnn] <;> ring
    simpa only [Function.comp_def, hcoeff] using hd
  exact hd'.hasDerivWithinAt

lemma inverse_pullback_simple_pole {a z : ℂ}
    (ha : a ≠ 0) (hz : z ≠ 0) (hza : z⁻¹ ≠ a) :
    -(z ^ 2)⁻¹ * (z⁻¹ - a)⁻¹ = (z - a⁻¹)⁻¹ - z⁻¹ := by
  have hzai : z ≠ a⁻¹ := by
    intro he
    apply hza
    rw [he, inv_inv]
  have hminus : 1 - z * a ≠ 0 := by
    intro he
    apply hza
    apply mul_left_cancel₀ hz
    calc
      z * z⁻¹ = 1 := mul_inv_cancel₀ hz
      _ = z * a := sub_eq_zero.mp he
  have hplus : -1 + z * a ≠ 0 := by
    intro he
    apply hminus
    linear_combination -he
  field_simp [hz, ha, sub_ne_zero.mpr hza, sub_ne_zero.mpr hzai, hminus, hplus]
  <;> ring <;> field_simp [hplus] <;> ring

lemma circleIntegral_inverse_pullback_simple_pole {a c : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hR : 0 ≤ R) (hzero : (0 : ℂ) ∉ closedBall c R)
    (hsep : a⁻¹ ∉ sphere c R) :
    (∮ z in C(c, R), -(z ^ 2)⁻¹ * (z⁻¹ - a)⁻¹) =
      (2 * Real.pi * Complex.I : ℂ) * (if a⁻¹ ∈ ball c R then 1 else 0) := by
  classical
  have hz : ∀ z ∈ sphere c R, z ≠ 0 := by
    intro z hz he
    exact hzero (he ▸ sphere_subset_closedBall hz)
  have hza : ∀ z ∈ sphere c R, z⁻¹ ≠ a := by
    intro z hz he
    apply hsep
    have hzinv : z = a⁻¹ := by rw [← he, inv_inv]
    exact hzinv ▸ hz
  have heq : (∮ z in C(c, R), -(z ^ 2)⁻¹ * (z⁻¹ - a)⁻¹) =
      ∮ z in C(c, R), (z - a⁻¹)⁻¹ - z⁻¹ := by
    apply circleIntegral.integral_congr hR
    intro z hzc
    exact inverse_pullback_simple_pole ha (hz z hzc) (hza z hzc)
  have hiA : CircleIntegrable (fun z : ℂ => (z - a⁻¹)⁻¹) c R := by
    simpa only [pow_zero, one_div] using powerRootFraction_circleIntegrable 0 hR hsep
  have hi0 : CircleIntegrable (fun z : ℂ => z⁻¹) c R := by
    simpa only [pow_zero, one_div, sub_zero] using powerRootFraction_circleIntegrable 0 hR
      (fun hs => hzero (sphere_subset_closedBall hs))
  rw [heq, circleIntegral.integral_sub hiA hi0]
  have hI0 : (∮ z in C(c, R), z⁻¹) = 0 := by
    simpa only [sub_zero] using circleIntegral_sub_inv_of_outside hR hzero
  rw [hI0, sub_zero]
  simpa only [pow_zero, one_div] using circleIntegral_powerRootFraction 0 hR hsep

/-- Actual change of contour on every rational partial-fraction basis. The
only geometry to supply is root membership and separation of the two circles;
there is no residue or contour-equality premise. For a true inversion image,
these geometry conditions will follow from its explicit disk equation. -/
theorem circleIntegral_inverse_pullback_power_basis (n : ℤ)
    {a c d : ℂ} {R S : ℝ} (ha : a ≠ 0) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hzero : (0 : ℂ) ∉ closedBall c R)
    (hsrc : a⁻¹ ∉ sphere c R) (htgt : a ∉ sphere d S)
    (hselect : a⁻¹ ∈ ball c R ↔ a ∈ ball d S) :
    (∮ z in C(c, R), -(z ^ 2)⁻¹ * (z⁻¹ - a) ^ n) =
      ∮ z in C(d, S), (z - a) ^ n := by
  classical
  by_cases hn : n = -1
  · subst n
    simp only [zpow_neg_one]
    rw [circleIntegral_inverse_pullback_simple_pole ha hR hzero hsrc]
    have ht := circleIntegral_powerRootFraction 0 hS htgt
    simp only [pow_zero, one_div] at ht
    rw [ht, hselect]
  · rw [circleIntegral.integral_sub_zpow_of_ne hn]
    apply circleIntegral_inverse_pullback_zpow_of_ne hn hR
    · intro z hz he
      exact hzero (he ▸ sphere_subset_closedBall hz)
    · intro z hz he
      apply hsrc
      have hzai : z = a⁻¹ := by rw [← he, inv_inv]
      exact hzai ▸ hz

end
end CGLMPBounds.Hardy
