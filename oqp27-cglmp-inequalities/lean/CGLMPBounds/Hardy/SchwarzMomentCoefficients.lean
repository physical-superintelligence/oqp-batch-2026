module

public import CGLMPBounds.Hardy.SchwarzMomentSeries
public import CGLMPBounds.Hardy.SchwarzSlitRepresentation
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Uniqueness

@[expose] public section


/-!
# The coefficient/moment identity in the second half of (C.8)

The genuine slit integral and exterior g/q identity give the germ
q(w)=q0+q1*w+w^2*integral rho(x)/(1-x*w). The preceding geometric expansion
and uniqueness of analytic power series identify each q_(m+2) with the actual
m-th density moment. The C.7 positive-cluster derivative identity is separate:
this file does not equate any q coefficient with that derivative by definition.
-/

open Complex Filter Set MeasureTheory Metric
open scoped Topology

namespace CGLMPBounds.Hardy
noncomputable section

lemma density_cauchyIntegral_inv (ρ : ℝ → ℝ) {w : ℂ} (hw : w ≠ 0) :
    (∫ x : ℝ, (ρ x : ℂ) / ((x : ℂ) - w⁻¹)) =
      -w * densityMomentTransform ρ w := by
  have hp : ∀ x : ℝ, (ρ x : ℂ) / ((x : ℂ) - w⁻¹) =
      -w * ((ρ x : ℂ) / (1 - (x : ℂ) * w)) := by
    intro x
    have he : (x : ℂ) - w⁻¹ = -w⁻¹ * (1 - (x : ℂ) * w) := by
      field_simp [hw]
      <;> ring
    rw [he, div_eq_mul_inv, mul_inv_rev, inv_neg, inv_inv, div_eq_mul_inv]
    ring
  simp_rw [hp]
  exact MeasureTheory.integral_const_mul _ _

/-- Injective imaginary-line approach gives the punctured accumulation
needed for analytic uniqueness; equality at the origin is not assumed. -/
lemma analytic_eventuallyEq_of_imaginary_line {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (heq : ∀ᶠ t : ℝ in 𝓝[≠] 0, f ((t : ℂ) * Complex.I) = g ((t : ℂ) * Complex.I)) :
    f =ᶠ[𝓝 0] g := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) := by fun_prop
      have hzero : Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (𝓝 0) (𝓝 (0 : ℂ)) := by
        simpa using hc.tendsto (0 : ℝ)
      exact hzero.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change t ≠ 0 at ht
      change (t : ℂ) * Complex.I ≠ 0
      exact mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  exact (hf.frequently_eq_iff_eventually_eq hg).mp (ht.frequently heq.frequently)

/-- The coefficient sequence obtained by placing two arbitrary affine terms
before the actual density moments. -/
def augmentedDensityMoment (ρ : ℝ → ℝ) (A B : ℂ) : ℕ → ℂ
  | 0 => A
  | 1 => B
  | n + 2 => (densityMoment ρ n : ℂ)

lemma hasFPowerSeriesAt_affine_densityMomentTransform {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hρi : Integrable ρ) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ x : ℝ, ρ x ≠ 0 → |x| ≤ a) (A B : ℂ) :
    HasFPowerSeriesAt (fun w : ℂ => A + B * w + w ^ 2 * densityMomentTransform ρ w)
      (FormalMultilinearSeries.ofScalars ℂ (augmentedDensityMoment ρ A B)) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  have hc : ContinuousAt (fun w : ℂ => a * ‖w‖) 0 := by fun_prop
  have he : ∀ᶠ w : ℂ in 𝓝 0, a * ‖w‖ < 1 :=
    hc.eventually_lt continuousAt_const (by simp)
  filter_upwards [he] with w hw
  have hm := (hasSum_densityMomentTransform hρ hρi ha hsupp hw).mul_left (w ^ 2)
  have ht : HasSum (fun n : ℕ => augmentedDensityMoment ρ A B (n + 2) * w ^ (n + 2))
      (w ^ 2 * densityMomentTransform ρ w) := by
    convert hm using 1
    ext n
    simp only [augmentedDensityMoment, pow_add]
    ring
  have hs := (hasSum_nat_add_iff (f := fun n => augmentedDensityMoment ρ A B n * w ^ n) 2).mp ht
  simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, add_zero,
    Finset.sum_range_succ, Finset.sum_range_zero, augmentedDensityMoment,
    pow_zero, pow_one, mul_one, mul_comm, add_comm, add_left_comm, add_assoc] using hs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- The actual q germ is recovered from the actual slit integral.
The imaginary line avoids all real poles before analytic uniqueness is used. -/
theorem exteriorClusterQ_eventually_eq_momentTransform
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) :
    exteriorClusterQ H Y =ᶠ[𝓝 0]
      (fun w : ℂ => exteriorTaylorCoefficient H Y 0 + exteriorTaylorCoefficient H Y 1 * w +
        w ^ 2 * densityMomentTransform (traceDensity H Y) w) := by
  have hf := analyticAt_exteriorClusterQ_zero Y hH hdet
  have hg := (hasFPowerSeriesAt_affine_densityMomentTransform
    (continuous_traceDensity H Y) (traceDensity_integrable hH hY hdet)
    (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (fun _ hx => traceDensity_support_abs_le hH hY hdet hx)
    (exteriorTaylorCoefficient H Y 0) (exteriorTaylorCoefficient H Y 1)).analyticAt
  apply analytic_eventuallyEq_of_imaginary_line hf hg
  obtain ⟨R, hR, hlarge⟩ := exists_reflectedPencilTrace_eq_exterior hH hY hdet
  have hc : ContinuousAt (fun t : ℝ => ‖(t : ℂ) * Complex.I‖) 0 := by fun_prop
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖(t : ℂ) * Complex.I‖ < R⁻¹ :=
    hc.eventually_lt continuousAt_const (by simpa using inv_pos.mpr hR)
  filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htn
  change t ≠ 0 at htn
  let w : ℂ := (t : ℂ) * Complex.I
  have hwn : w ≠ 0 := mul_ne_zero (by exact_mod_cast htn) Complex.I_ne_zero
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hwn
  have hzlarge : R < ‖w⁻¹‖ := by
    rw [norm_inv]
    have h := (inv_lt_inv₀ (inv_pos.mpr hR) hwp).mpr ht
    simpa only [inv_inv] using h
  have hwim : w.im ≠ 0 := by simpa [w] using htn
  have hzim : w⁻¹.im ≠ 0 := by
    rw [Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr hwim) (Complex.normSq_pos.mpr hwn).ne'
  have hrep := regularizedReflectedTrace_eq_integral hH hY hdet hzim
  rw [regularizedReflectedTrace, hlarge w⁻¹ hzlarge, inv_inv,
    density_cauchyIntegral_inv (traceDensity H Y) hwn] at hrep
  have hm := congrArg (fun u : ℂ => -w * u) hrep
  field_simp [hwn] at hm
  change exteriorClusterQ H Y w = _
  linear_combination hm

/-- The second identity of (C.8), with full-line Lebesgue moments and the
actual Taylor coefficients of the literal normalized negative-cluster q. -/
theorem traceDensity_moment_eq_exteriorTaylorCoefficient
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (m : ℕ) :
    ((∫ x : ℝ, x ^ m * traceDensity H Y x : ℝ) : ℂ) =
      exteriorTaylorCoefficient H Y (m + 2) := by
  have hq := (analyticAt_exteriorClusterQ_zero Y hH hdet).hasFPowerSeriesAt
  have hm := hasFPowerSeriesAt_affine_densityMomentTransform
    (continuous_traceDensity H Y) (traceDensity_integrable hH hY hdet)
    (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (fun _ hx => traceDensity_support_abs_le hH hY hdet hx)
    (exteriorTaylorCoefficient H Y 0) (exteriorTaylorCoefficient H Y 1)
  have he := hq.eq_formalMultilinearSeries_of_eventually hm
    (exteriorClusterQ_eventually_eq_momentTransform hH hY hdet)
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff (m + 2)) he
  simpa only [FormalMultilinearSeries.coeff_ofScalars, augmentedDensityMoment,
    exteriorTaylorCoefficient, densityMoment] using hc.symm

end
end CGLMPBounds.Hardy
