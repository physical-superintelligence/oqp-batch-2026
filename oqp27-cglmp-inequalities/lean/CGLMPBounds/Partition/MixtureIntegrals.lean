module

public import CGLMPBounds.Partition.MixtureDensity

@[expose] public section


/-! Actual bounded-observable and event probabilities of positive Fourier
mixtures. Every mixture is the literal withDensity measure. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

theorem integral_fourierMixtureMeasure (d : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) (hmass : (∑' n, a n) ≤ 1)
    (f : (Fin d → ℝ) → ℝ) :
    (∫ T, f T ∂fourierMixtureMeasure d a) =
      ∫ T, fourierMixtureDensity d a T * f T ∂boundaryProductMeasure d := by
  have hm := (continuous_fourierMixtureDensity d a ha0 ha).measurable.ennreal_ofReal
  have htop : ∀ᵐ T ∂boundaryProductMeasure d,
      ENNReal.ofReal (fourierMixtureDensity d a T) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  unfold fourierMixtureMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hm htop f]
  apply integral_congr_ae
  filter_upwards [] with T
  rw [ENNReal.toReal_ofReal (fourierMixtureDensity_nonneg d a ha0 hmass T)]
  rfl

lemma integral_fourierBoundaryMeasure_real (d n : ℕ) (f : (Fin d → ℝ) → ℝ) :
    (∫ T, f T ∂fourierBoundaryMeasure d n) =
      ∫ T, fourierBoundaryDensity d n T * f T ∂boundaryProductMeasure d := by
  have hm := (continuous_fourierBoundaryDensity d n).measurable.ennreal_ofReal
  have htop : ∀ᵐ T ∂boundaryProductMeasure d,
      ENNReal.ofReal (fourierBoundaryDensity d n T) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  unfold fourierBoundaryMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hm htop f]
  apply integral_congr_ae
  filter_upwards [] with T
  rw [ENNReal.toReal_ofReal (fourierBoundaryDensity_nonneg d n T)]
  rfl

theorem integral_fourierMixtureDensity_mul (d : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a)
    (f : (Fin d → ℝ) → ℝ)
    (hf : AEStronglyMeasurable f (boundaryProductMeasure d))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ T, ‖f T‖ ≤ C) :
    (∫ T, fourierMixtureDensity d a T * f T ∂boundaryProductMeasure d) =
      fourierMixtureResidual a * (∫ T, f T ∂boundaryProductMeasure d) +
        ∑' n, a n * (∫ T, fourierBoundaryDensity d (n + 1) T * f T
          ∂boundaryProductMeasure d) := by
  have hfi : Integrable f (boundaryProductMeasure d) :=
    (integrable_const C).mono' hf (Filter.Eventually.of_forall hbound)
  have hprod (n : ℕ) : Integrable (fun T : Fin d → ℝ =>
      a n * fourierBoundaryDensity d (n + 1) T * f T) (boundaryProductMeasure d) :=
    ((integrable_fourierBoundaryDensity d (n + 1)).const_mul (a n)).mul_bdd
      hf (Filter.Eventually.of_forall hbound)
  have hnorm (n : ℕ) (T : Fin d → ℝ) :
      ‖a n * fourierBoundaryDensity d (n + 1) T * f T‖ ≤ a n * d * C := by
    rw [norm_mul]
    exact mul_le_mul (norm_weighted_fourierBoundaryDensity_le d a ha0 n T)
      (hbound T) (norm_nonneg _) (mul_nonneg (ha0 n) (Nat.cast_nonneg _))
  have hnormint (n : ℕ) :
      (∫ T : Fin d → ℝ, ‖a n * fourierBoundaryDensity d (n + 1) T * f T‖
        ∂boundaryProductMeasure d) ≤ a n * d * C := by
    calc
      _ ≤ ∫ _ : Fin d → ℝ, a n * d * C ∂boundaryProductMeasure d :=
        integral_mono (hprod n).norm (integrable_const _) (hnorm n)
      _ = _ := by simp
  have hnormsum : Summable (fun n => ∫ T : Fin d → ℝ,
      ‖a n * fourierBoundaryDensity d (n + 1) T * f T‖ ∂boundaryProductMeasure d) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun T => norm_nonneg _))
      hnormint ((ha.mul_right (d : ℝ)).mul_right C)
  have hint := integral_tsum_of_summable_integral_norm hprod hnormsum
  have hwhole := (integrable_fourierMixtureDensity d a ha0 ha).mul_bdd
    hf (Filter.Eventually.of_forall hbound)
  have hconst := hfi.const_mul (fourierMixtureResidual a)
  have hseries : Integrable (fun T : Fin d → ℝ =>
      ∑' n, a n * fourierBoundaryDensity d (n + 1) T * f T)
      (boundaryProductMeasure d) := by
    apply (hwhole.sub hconst).congr
    filter_upwards [] with T
    rw [tsum_mul_right]
    dsimp [fourierMixtureDensity]
    ring
  calc
    _ = ∫ T : Fin d → ℝ,
        fourierMixtureResidual a * f T +
          ∑' n, a n * fourierBoundaryDensity d (n + 1) T * f T
            ∂boundaryProductMeasure d := by
      apply integral_congr_ae
      filter_upwards [] with T
      rw [tsum_mul_right]
      dsimp [fourierMixtureDensity]
      ring
    _ = _ := by
      rw [integral_add hconst hseries, integral_const_mul, ← hint]
      congr 1
      apply tsum_congr
      intro n
      simp only [mul_assoc, integral_const_mul]

theorem fourierMixtureMeasure_real (d : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) (hmass : (∑' n, a n) ≤ 1)
    (E : Set (Fin d → ℝ)) (hE : MeasurableSet E) :
    (fourierMixtureMeasure d a).real E =
      fourierMixtureResidual a * (boundaryProductMeasure d).real E +
        ∑' n, a n * (fourierBoundaryMeasure d (n + 1)).real E := by
  have hb : ∀ T : Fin d → ℝ, ‖E.indicator (fun _ => (1 : ℝ)) T‖ ≤ 1 := by
    intro T
    by_cases hT : T ∈ E <;> simp [Set.indicator_apply, hT]
  have hstart : (fourierMixtureMeasure d a).real E =
      ∫ T, E.indicator (fun _ => (1 : ℝ)) T ∂fourierMixtureMeasure d a := by
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := fourierMixtureMeasure d a) (1 : ℝ) hE).symm
  rw [hstart, integral_fourierMixtureMeasure d a ha0 ha hmass,
    integral_fourierMixtureDensity_mul d a ha0 ha _
      ((measurable_const.indicator hE).aestronglyMeasurable) 1 zero_le_one hb]
  simp only [integral_indicator_const _ hE, smul_eq_mul, mul_one]
  congr 1
  apply tsum_congr
  intro n
  rw [← integral_fourierBoundaryMeasure_real, integral_indicator_const _ hE]
  simp

end
end CGLMPBounds.Partition
