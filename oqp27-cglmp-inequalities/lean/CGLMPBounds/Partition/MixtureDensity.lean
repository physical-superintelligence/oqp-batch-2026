module

public import CGLMPBounds.Defs.PartitionMixture
public import CGLMPBounds.Partition.DensityNormalization

@[expose] public section


/-! Positive summable mixtures of the literal Fourier-power densities.
These are structural mixture results, not a proof that the particular source
function v has the required positive Fourier expansion. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

lemma norm_weighted_fourierBoundaryDensity_le (d : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (n : ℕ) (T : Fin d → ℝ) :
    ‖a n * fourierBoundaryDensity d (n + 1) T‖ ≤ a n * d := by
  rw [Real.norm_of_nonneg
    (mul_nonneg (ha0 n) (fourierBoundaryDensity_nonneg d (n + 1) T))]
  exact mul_le_mul_of_nonneg_left (fourierBoundaryDensity_le d (n + 1) T) (ha0 n)

lemma summable_weighted_fourierBoundaryDensity (d : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) (T : Fin d → ℝ) :
    Summable (fun n => a n * fourierBoundaryDensity d (n + 1) T) := by
  exact (ha.mul_right (d : ℝ)).of_norm_bounded
    (fun n => norm_weighted_fourierBoundaryDensity_le d a ha0 n T)

theorem continuous_fourierMixtureDensity (d : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) :
    Continuous (fourierMixtureDensity d a) := by
  apply continuous_const.add
  exact continuous_tsum
    (fun n => continuous_const.mul (continuous_fourierBoundaryDensity d (n + 1)))
    (ha.mul_right (d : ℝ))
    (fun n T => norm_weighted_fourierBoundaryDensity_le d a ha0 n T)

theorem fourierMixtureDensity_lower (d : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (T : Fin d → ℝ) :
    fourierMixtureResidual a ≤ fourierMixtureDensity d a T := by
  apply le_add_of_nonneg_right
  exact tsum_nonneg (fun n =>
    mul_nonneg (ha0 n) (fourierBoundaryDensity_nonneg d (n + 1) T))

theorem fourierMixtureDensity_nonneg (d : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (hmass : (∑' n, a n) ≤ 1) (T : Fin d → ℝ) :
    0 ≤ fourierMixtureDensity d a T := by
  exact (sub_nonneg.mpr hmass).trans (fourierMixtureDensity_lower d a ha0 T)

lemma norm_fourierMixtureDensity_le (d : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) (T : Fin d → ℝ) :
    ‖fourierMixtureDensity d a T‖ ≤
      ‖fourierMixtureResidual a‖ + (∑' n, a n) * d := by
  calc
    _ ≤ ‖fourierMixtureResidual a‖ +
        ‖∑' n, a n * fourierBoundaryDensity d (n + 1) T‖ := norm_add_le _ _
    _ ≤ ‖fourierMixtureResidual a‖ + ∑' n, a n * (d : ℝ) := by
      apply add_le_add le_rfl
      exact tsum_of_norm_bounded (ha.mul_right (d : ℝ)).hasSum
        (fun n => norm_weighted_fourierBoundaryDensity_le d a ha0 n T)
    _ = _ := by rw [tsum_mul_right]

theorem integrable_fourierMixtureDensity (d : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) :
    Integrable (fourierMixtureDensity d a) (boundaryProductMeasure d) := by
  apply (integrable_const (‖fourierMixtureResidual a‖ + (∑' n, a n) * d)).mono'
    (continuous_fourierMixtureDensity d a ha0 ha).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_fourierMixtureDensity_le d a ha0 ha)

lemma integral_weighted_fourierBoundaryDensity_norm (d : ℕ) (hd : 0 < d)
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (n : ℕ) :
    (∫ T : Fin d → ℝ, ‖a n * fourierBoundaryDensity d (n + 1) T‖
      ∂boundaryProductMeasure d) = a n := by
  simp_rw [Real.norm_of_nonneg
    (mul_nonneg (ha0 n) (fourierBoundaryDensity_nonneg d (n + 1) _))]
  rw [integral_const_mul, integral_fourierBoundaryDensity d (n + 1) hd (by omega),
    mul_one]

theorem integral_fourierMixtureDensity (d : ℕ) (hd : 0 < d)
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) :
    (∫ T, fourierMixtureDensity d a T ∂boundaryProductMeasure d) = 1 := by
  have hseries : Integrable (fun T : Fin d → ℝ =>
      ∑' n, a n * fourierBoundaryDensity d (n + 1) T) (boundaryProductMeasure d) := by
    have h := (integrable_fourierMixtureDensity d a ha0 ha).sub
      (integrable_const (fourierMixtureResidual a))
    change Integrable (fun T : Fin d → ℝ =>
      fourierMixtureDensity d a T - fourierMixtureResidual a)
        (boundaryProductMeasure d) at h
    simpa only [fourierMixtureDensity, add_sub_cancel_left] using h
  have hint := integral_tsum_of_summable_integral_norm
    (fun n => (integrable_fourierBoundaryDensity d (n + 1)).const_mul (a n))
    (by simpa only [integral_weighted_fourierBoundaryDensity_norm d hd a ha0] using ha)
  unfold fourierMixtureDensity
  rw [integral_add (integrable_const _) hseries, ← hint]
  simp only [integral_const_mul, integral_fourierBoundaryDensity d _ hd (Nat.succ_pos _),
    mul_one]
  simp [fourierMixtureResidual]

theorem fourierMixtureMeasure_isProbabilityMeasure (d : ℕ) (hd : 0 < d)
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a)
    (hmass : (∑' n, a n) ≤ 1) :
    IsProbabilityMeasure (fourierMixtureMeasure d a) := by
  refine ⟨?_⟩
  rw [fourierMixtureMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_fourierMixtureDensity d a ha0 ha)
      (Filter.Eventually.of_forall (fourierMixtureDensity_nonneg d a ha0 hmass)),
    integral_fourierMixtureDensity d hd a ha0 ha]
  simp

end
end CGLMPBounds.Partition
