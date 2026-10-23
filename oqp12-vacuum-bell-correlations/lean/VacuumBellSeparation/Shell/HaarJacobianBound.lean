module

public import VacuumBellSeparation.Shell.HaarJacobianCoordinates

@[expose] public section


/-!
# A quantitative measure bound from a genuine Jacobian estimate

The constant carries the fixed Haar-coordinate normalization. A bound on
the actual Jacobian gives the needed reverse integral control for every
nonnegative weight, without a measurability assumption on that weight.
-/

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]

theorem lintegral_image_le_linearHaarScale_jacobian_bound (J : E ≃L[ℝ] F)
    {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : Set.InjOn f s) {C : ℝ}
    (hC : ∀ x ∈ s, |(J.symm.toContinuousLinearMap.comp (f' x)).det| ≤ C)
    (g : F → ℝ≥0∞) :
    (∫⁻ y in f '' s, g y ∂ν) ≤
      (linearHaarScale μ ν J : ℝ≥0∞) * ENNReal.ofReal C *
        ∫⁻ x in s, g (f x) ∂μ := by
  rw [lintegral_image_eq_linearHaarScale_jacobian μ ν J hs hf' hinj]
  calc
    _ ≤ (linearHaarScale μ ν J : ℝ≥0∞) *
        ∫⁻ x in s, ENNReal.ofReal C * g (f x) ∂μ := by
      apply _root_.mul_le_mul_right
      apply setLIntegral_mono' hs
      intro x hx
      exact _root_.mul_le_mul_left (ENNReal.ofReal_le_ofReal (hC x hx)) _
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact (mul_assoc _ _ _).symm

theorem lintegral_subset_image_le_linearHaarScale_jacobian_bound (J : E ≃L[ℝ] F)
    {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : Set.InjOn f s) {C : ℝ}
    (hC : ∀ x ∈ s, |(J.symm.toContinuousLinearMap.comp (f' x)).det| ≤ C)
    {t : Set F} (ht : t ⊆ f '' s) (g : F → ℝ≥0∞) :
    (∫⁻ y in t, g y ∂ν) ≤
      (linearHaarScale μ ν J : ℝ≥0∞) * ENNReal.ofReal C *
        ∫⁻ x in s, g (f x) ∂μ :=
  (lintegral_mono_set ht).trans
    (lintegral_image_le_linearHaarScale_jacobian_bound μ ν J hs hf' hinj hC g)

end VacuumBellSeparation
