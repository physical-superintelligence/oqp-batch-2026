module

public import CGLMPBounds.Hardy.SchwarzReflectedExterior
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Normed.Field.Lemmas

@[expose] public section


/-!
# Subtracting the affine exterior part of the reflected source function

The genuine q has an analytic second divided difference at zero. This gives an
exact exterior expression and a 1/|z| bound for g(z)+q₀z+q₁, on both sides of
the slit. The function therefore tends to zero at infinity. These are inputs
for the slit-contour argument, not an assumed Cauchy-transform representation.

Source: supplement printed p.8, the affine term in C.8.
-/

open Complex Matrix Filter Set Metric Bornology
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- Actual second divided difference with Mathlib's derivative-based removable
values at zero. It is not defined through a desired moment sequence. -/
def exteriorSecondDifference (H Y : Matrix ι ι ℂ) : ℂ → ℂ :=
  dslope (dslope (exteriorClusterQ H Y) 0) 0

@[simp] theorem exteriorTaylorCoefficient_one (H Y : Matrix ι ι ℂ) :
    exteriorTaylorCoefficient H Y 1 = deriv (exteriorClusterQ H Y) 0 := by
  simp [exteriorTaylorCoefficient, iteratedDeriv_one]

theorem analyticAt_exteriorSecondDifference_zero {H : Matrix ι ι ℂ}
    (Y : Matrix ι ι ℂ) (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    AnalyticAt ℂ (exteriorSecondDifference H Y) 0 := by
  obtain ⟨p, hp⟩ := analyticAt_exteriorClusterQ_zero Y hH hdet
  exact hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope.analyticAt

/-- Exact second-order decomposition, including w=0. -/
theorem exteriorClusterQ_eq_affine_add_secondDifference
    (H Y : Matrix ι ι ℂ) (w : ℂ) :
    exteriorClusterQ H Y w = exteriorTaylorCoefficient H Y 0 +
      exteriorTaylorCoefficient H Y 1 * w + w ^ 2 * exteriorSecondDifference H Y w := by
  have h₀ : w * dslope (exteriorClusterQ H Y) 0 w =
      exteriorClusterQ H Y w - exteriorClusterQ H Y 0 := by
    simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope (exteriorClusterQ H Y) 0 w
  have h₁ : w * exteriorSecondDifference H Y w =
      dslope (exteriorClusterQ H Y) 0 w - deriv (exteriorClusterQ H Y) 0 := by
    simpa only [sub_zero, smul_eq_mul, dslope_same, exteriorSecondDifference] using
      sub_smul_dslope (dslope (exteriorClusterQ H Y) 0) 0 w
  rw [exteriorTaylorCoefficient_zero, exteriorTaylorCoefficient_one]
  linear_combination -h₀ - w * h₁

/-- The source's affine part is removed with its actual Taylor coefficients. -/
def regularizedReflectedTrace (H Y : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  reflectedPencilTrace H Y z + exteriorTaylorCoefficient H Y 0 * z +
    exteriorTaylorCoefficient H Y 1

theorem analyticOnNhd_regularizedReflectedTrace
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) :
    AnalyticOnNhd ℂ (regularizedReflectedTrace H Y) (spectralSlit Y)ᶜ := by
  intro z hz
  exact ((analyticOnNhd_reflectedPencilTrace hH hY hdet z hz).add
    (analyticAt_const.mul analyticAt_id)).add analyticAt_const

/-- Removing the real affine term preserves precisely the source jump. -/
theorem regularizedReflectedTrace_sub_conj_real
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (x : ℝ) :
    regularizedReflectedTrace H Y (x : ℂ) -
      star (regularizedReflectedTrace H Y (x : ℂ)) =
        (2 * Real.pi * Complex.I : ℂ) * (traceDensity H Y x : ℂ) := by
  have hxr : star (x : ℂ) = (x : ℂ) := by simp [Complex.star_def]
  simp only [regularizedReflectedTrace, reflectedPencilTrace_real, star_add, star_mul',
    hxr, exteriorTaylorCoefficient_star hH hY hdet]
  convert pencilUpperBoundaryExtension_sub_conj hH hY hdet x using 1 <;> ring

/-- A genuine full exterior expression for the regularized source g. -/
theorem exists_regularizedReflectedTrace_eq_secondDifference
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R < ‖z‖ →
      regularizedReflectedTrace H Y z = (-z⁻¹) * exteriorSecondDifference H Y z⁻¹ := by
  obtain ⟨R, hR, heq⟩ := exists_reflectedPencilTrace_eq_exterior hH hY hdet
  refine ⟨R, hR, ?_⟩
  intro z hz
  have hzn : z ≠ 0 := norm_pos_iff.mp (hR.trans hz)
  rw [regularizedReflectedTrace, heq z hz,
    exteriorClusterQ_eq_affine_add_secondDifference H Y z⁻¹]
  field_simp [hzn] <;> ring

/-- The concrete analytic remainder yields an actual O(1/|z|) bound. -/
theorem exists_regularizedReflectedTrace_norm_bound
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ℂ, R < ‖z‖ →
      ‖regularizedReflectedTrace H Y z‖ ≤ C / ‖z‖ := by
  obtain ⟨R₀, hR₀, heq⟩ := exists_regularizedReflectedTrace_eq_secondDifference hH hY hdet
  let C : ℝ := ‖exteriorSecondDifference H Y 0‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ᶠ w in 𝓝 (0 : ℂ), ‖exteriorSecondDifference H Y w‖ < C :=
    (analyticAt_exteriorSecondDifference_zero Y hH hdet).continuousAt.norm.eventually_lt
      continuousAt_const (lt_add_one _)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff_ball.mp hbound
  refine ⟨max R₀ δ⁻¹, C, hR₀.trans_le (le_max_left _ _), hC, ?_⟩
  intro z hz
  have hz₀ : R₀ < ‖z‖ := (le_max_left _ _).trans_lt hz
  have hsmall : ‖z⁻¹‖ < δ := norm_inv_lt_of_inv_lt_norm hδ ((le_max_right _ _).trans_lt hz)
  have htail : ‖exteriorSecondDifference H Y z⁻¹‖ ≤ C :=
    (hδbound z⁻¹ (by simpa only [mem_ball_iff_norm, sub_zero] using hsmall)).le
  rw [heq z hz₀, norm_mul, norm_neg, norm_inv]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr (norm_nonneg z))

/-- The regularized source trace tends to zero at complex infinity. -/
theorem tendsto_regularizedReflectedTrace_zero
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) :
    Tendsto (regularizedReflectedTrace H Y) (cobounded ℂ) (𝓝 0) := by
  obtain ⟨R, hR, heq⟩ := exists_regularizedReflectedTrace_eq_secondDifference hH hY hdet
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cobounded ℂ) (𝓝 0) := tendsto_inv₀_cobounded
  have ht := (analyticAt_exteriorSecondDifference_zero Y hH hdet).continuousAt.tendsto.comp hi
  have hlim : Tendsto (fun z : ℂ => (-z⁻¹) * exteriorSecondDifference H Y z⁻¹)
      (cobounded ℂ) (𝓝 0) := by
    simpa only [Function.comp_apply, neg_zero, zero_mul] using! hi.neg.mul ht
  apply Tendsto.congr' _ hlim
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) (R + 1)] with z hz
  exact (heq z (by linarith)).symm

end
end CGLMPBounds.Hardy
