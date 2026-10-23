module

public import CGLMPBounds.Hardy.DensityIntegrability
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


/-!
# Actual moment series of the compactly supported trace density

The auxiliary generating function is the literal integral rho(x)/(1-x*w).
The geometric series and dominated convergence identify its coefficients with
actual full-line moments. No coefficient of the source contour function q is
used in these definitions; identifying those coefficients is a further step.

Pinned APIs reused: `hasSum_geometric_of_norm_lt_one`,
`MeasureTheory.hasSum_integral_of_dominated_convergence`, and the scalar
`hasFPowerSeriesAt_iff` (which avoids an artificial assumed convergence radius).
-/

open Complex Filter Set MeasureTheory
open scoped Topology

namespace CGLMPBounds.Hardy
noncomputable section

/-- The complex-valued Cauchy moment generating integral, with its literal
value at zero. It is used only where the support is separated from the pole. -/
def densityMomentTransform (ρ : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, (ρ x : ℂ) / (1 - (x : ℂ) * w)

/-- Actual real moments, with no coefficient or spectral-functional oracle. -/
def densityMoment (ρ : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ n * ρ x

lemma hasSum_densityMomentTransform {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hρi : Integrable ρ) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ x : ℝ, ρ x ≠ 0 → |x| ≤ a)
    {w : ℂ} (hw : a * ‖w‖ < 1) :
    HasSum (fun n : ℕ => (densityMoment ρ n : ℂ) * w ^ n)
      (densityMomentTransform ρ w) := by
  let r : ℝ := a * ‖w‖
  have hr0 : 0 ≤ r := mul_nonneg ha (norm_nonneg w)
  have hr1 : r < 1 := hw
  have hgeom : Summable (fun n : ℕ => r ^ n) :=
    (hasSum_geometric_of_lt_one hr0 hr1).summable
  have hbound : ∀ n x, ‖(ρ x : ℂ) * ((x : ℂ) * w) ^ n‖ ≤ ‖ρ x‖ * r ^ n := by
    intro n x
    by_cases hx : ρ x = 0
    · simp [hx, hr0]
    · simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hsupp x hx) (norm_nonneg w)) n)
        (abs_nonneg (ρ x))
  have hsum := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume)
    (F := fun n x => (ρ x : ℂ) * ((x : ℂ) * w) ^ n)
    (f := fun x => (ρ x : ℂ) / (1 - (x : ℂ) * w))
    (fun n x => ‖ρ x‖ * r ^ n)
    (fun n => by
      have hc : Continuous (fun x : ℝ => (ρ x : ℂ) * ((x : ℂ) * w) ^ n) := by
        fun_prop
      exact hc.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (hbound n))
    (Filter.Eventually.of_forall (fun x => hgeom.mul_left ‖ρ x‖))
    (by
      simpa only [tsum_mul_left] using hρi.norm.mul_const (∑' n : ℕ, r ^ n))
    (Filter.Eventually.of_forall (by
      intro x
      by_cases hx : ρ x = 0
      · simp only [hx, Complex.ofReal_zero, zero_mul, zero_div]
        exact hasSum_zero
      · have hxw : ‖(x : ℂ) * w‖ < 1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact (mul_le_mul_of_nonneg_right (hsupp x hx) (norm_nonneg w)).trans_lt hw
        simpa only [div_eq_mul_inv] using
          (hasSum_geometric_of_norm_lt_one hxw).mul_left (ρ x : ℂ)))
  have hterm (n : ℕ) :
      (∫ x : ℝ, (ρ x : ℂ) * ((x : ℂ) * w) ^ n) =
        (densityMoment ρ n : ℂ) * w ^ n := by
    have he : (fun x : ℝ => (ρ x : ℂ) * ((x : ℂ) * w) ^ n) =
        (fun x : ℝ => ((x ^ n * ρ x : ℝ) : ℂ) * w ^ n) := by
      funext x
      push_cast
      rw [mul_pow]
      ring
    rw [he, MeasureTheory.integral_mul_const, integral_complex_ofReal]
    rfl
  simpa only [hterm, densityMomentTransform] using hsum

lemma hasFPowerSeriesAt_densityMomentTransform {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hρi : Integrable ρ) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ x : ℝ, ρ x ≠ 0 → |x| ≤ a) :
    HasFPowerSeriesAt (densityMomentTransform ρ)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (densityMoment ρ n : ℂ))) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  have hc : ContinuousAt (fun w : ℂ => a * ‖w‖) 0 := by fun_prop
  have he : ∀ᶠ w : ℂ in 𝓝 0, a * ‖w‖ < 1 :=
    hc.eventually_lt continuousAt_const (by simp)
  filter_upwards [he] with w hw
  simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add,
    mul_comm] using hasSum_densityMomentTransform hρ hρi ha hsupp hw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma traceDensity_support_abs_le {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {x : ℝ} (hx : traceDensity H Y x ≠ 0) :
    |x| ≤ |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)| := by
  have hmem : x ∈ Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y)) := by
    by_contra hn
    exact hx (traceDensity_eq_zero_outside_spectralInterval hH hY hdet hn)
  apply abs_le.mpr
  constructor
  · have hlo := neg_abs_le (sInf (spectrum ℝ Y))
    have hnonneg := abs_nonneg (sSup (spectrum ℝ Y))
    linarith [hmem.1]
  · have hhi := le_abs_self (sSup (spectrum ℝ Y))
    have hnonneg := abs_nonneg (sInf (spectrum ℝ Y))
    linarith [hmem.2]

/-- The actual density has a convergent moment generating power series.
Hermitian/invertible source assumptions discharge every analytic premise. -/
theorem traceDensity_hasFPowerSeriesAt_momentTransform
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) :
    HasFPowerSeriesAt (densityMomentTransform (traceDensity H Y))
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => (densityMoment (traceDensity H Y) n : ℂ))) 0 :=
  hasFPowerSeriesAt_densityMomentTransform (continuous_traceDensity H Y)
    (traceDensity_integrable hH hY hdet)
    (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (fun _ hx => traceDensity_support_abs_le hH hY hdet hx)

end
end CGLMPBounds.Hardy
