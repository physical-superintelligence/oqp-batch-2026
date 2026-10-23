module

public import CGLMPBounds.Hardy.SchwarzAffineRemainder
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section


/-!
# Vanishing of the genuine outer-circle contribution

The already constructed regularized source function is analytic off the exact
slit and decays as 1/|w|. This gives actual circle integrability for sufficiently
large radii and a direct norm estimate for its Cauchy-kernel integral. The
outer-circle contribution tends to zero without an assumed contour-limit law.

This is an ingredient for C.8, not the remaining slit deformation identity.
-/

open Complex Matrix Filter Set Metric
open scoped Topology Interval Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

/-- The elementary length-times-sup estimate for a Cauchy kernel on a large
circle, using the reverse triangle inequality for its denominator. -/
lemma norm_circleIntegral_kernel_le_of_decay
    (f : ℂ → ℂ) (z : ℂ) {R C : ℝ} (hC : 0 ≤ C) (hz : ‖z‖ < R)
    (hf : ∀ w ∈ sphere (0 : ℂ) R, ‖f w‖ ≤ C / R) :
    ‖∮ w in C(0, R), f w / (w - z)‖ ≤ (2 * Real.pi * C) / (R - ‖z‖) := by
  have hR : 0 < R := (norm_nonneg z).trans_lt hz
  have hd : 0 < R - ‖z‖ := sub_pos.mpr hz
  have hbound : ∀ w ∈ sphere (0 : ℂ) R,
      ‖f w / (w - z)‖ ≤ (C / R) / (R - ‖z‖) := by
    intro w hw
    have hnorm : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right] using hw
    have hden : R - ‖z‖ ≤ ‖w - z‖ := by simpa only [hnorm] using norm_sub_norm_le w z
    rw [norm_div]
    exact (div_le_div_of_nonneg_right (hf w hw) (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left (div_nonneg hC hR.le) hd hden)
  calc
    ‖∮ w in C(0, R), f w / (w - z)‖ ≤
        2 * Real.pi * R * ((C / R) / (R - ‖z‖)) :=
      circleIntegral.norm_integral_le_of_norm_le_const hR.le hbound
    _ = (2 * Real.pi * C) / (R - ‖z‖) := by
      field_simp [hR.ne', hd.ne'] <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma spectralSlit_subset_closedBall (Y : Matrix ι ι ℂ) :
    spectralSlit Y ⊆ closedBall (0 : ℂ)
      (|sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)|) := by
  intro w hw
  have hwe : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hw.1]
  have ha : |w.re| ≤ |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)| := by
    apply abs_le.mpr
    constructor
    · have h₁ := neg_abs_le (sInf (spectrum ℝ Y))
      have h₂ := abs_nonneg (sSup (spectrum ℝ Y))
      linarith [hw.2.1]
    · have h₁ := le_abs_self (sSup (spectrum ℝ Y))
      have h₂ := abs_nonneg (sInf (spectrum ℝ Y))
      linarith [hw.2.2]
  rw [mem_closedBall, dist_zero_right, hwe, Complex.norm_real, Real.norm_eq_abs]
  exact ha

/-- Actual integrability of the large-circle Cauchy kernel, rather than relying
on the totalized zero value of a nonintegrable Bochner integral. -/
theorem eventually_circleIntegrable_regularized_kernel
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (z : ℂ) :
    ∀ᶠ R : ℝ in atTop,
      CircleIntegrable (fun w => regularizedReflectedTrace H Y w / (w - z)) 0 R := by
  let M : ℝ := |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)|
  filter_upwards [eventually_gt_atTop (max M ‖z‖)] with R hR
  have hRz : ‖z‖ < R := (le_max_right _ _).trans_lt hR
  have hRp : 0 < R := (norm_nonneg z).trans_lt hRz
  have hs : sphere (0 : ℂ) R ⊆ (spectralSlit Y)ᶜ := by
    intro w hw hslit
    have hn : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right] using hw
    have hb := spectralSlit_subset_closedBall Y hslit
    have : ‖w‖ ≤ M := by simpa only [mem_closedBall, dist_zero_right] using hb
    rw [hn] at this
    exact (not_le.mpr ((le_max_left _ _).trans_lt hR)) this
  apply ContinuousOn.circleIntegrable hRp.le
  apply ((analyticOnNhd_regularizedReflectedTrace hH hY hdet).continuousOn.mono hs).div
    (continuous_id.sub continuous_const).continuousOn
  intro w hw he
  have hwe : w = z := sub_eq_zero.mp he
  have hn : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right] using hw
  rw [hwe] at hn
  exact (ne_of_lt hRz) hn

/-- The actual outer-circle Cauchy integral of the source remainder vanishes
at infinity for every fixed complex pole z. -/
theorem tendsto_regularized_outerCircle_zero
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (z : ℂ) :
    Tendsto (fun R : ℝ =>
      ∮ w in C(0, R), regularizedReflectedTrace H Y w / (w - z)) atTop (𝓝 0) := by
  obtain ⟨R₀, C, hR₀, hC, hbound⟩ := exists_regularizedReflectedTrace_norm_bound hH hY hdet
  have hb : ∀ᶠ R : ℝ in atTop,
      ‖∮ w in C(0, R), regularizedReflectedTrace H Y w / (w - z)‖ ≤
        (2 * Real.pi * C) / (R - ‖z‖) := by
    filter_upwards [eventually_gt_atTop (max R₀ ‖z‖)] with R hR
    apply norm_circleIntegral_kernel_le_of_decay _ z hC.le ((le_max_right _ _).trans_lt hR)
    intro w hw
    have hn : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right] using hw
    simpa only [hn] using hbound w (by rw [hn]; exact (le_max_left _ _).trans_lt hR)
  apply squeeze_zero_norm' hb
  apply tendsto_const_nhds.div_atTop
  simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-‖z‖) tendsto_id

end
end CGLMPBounds.Hardy
