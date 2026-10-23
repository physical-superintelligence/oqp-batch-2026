module

public import CGLMPBounds.Hardy.PositivePinchingCycleMoments
public import CGLMPBounds.Hardy.PositivePinchingFiniteMeasure

@[expose] public section


/-! Integrating the literal C.13 slice moment against an arbitrary continuous
x weight. The joint integrability needed for Fubini is derived from the actual
finite measure and its compact support, then transferred through its density. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Complex MeasureTheory Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma positivePinching_integral_eq_density_integral (B Y : Matrix ι ι ℂ)
    (f : (ℝ × ℝ) → ℂ) :
    (∫ p, f p ∂positivePinchingMeasure B Y) =
      ∫ p : ℝ × ℝ, (positivePinchingDensity B Y p : ℂ) * f p := by
  rw [positivePinchingMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_positivePinchingDensity B Y).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [ENNReal.toReal_ofReal (positivePinching_density_nonneg B Y p), Complex.real_smul]

lemma positivePinching_continuous_density_product_integrable
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {f : (ℝ × ℝ) → ℂ} (hf : Continuous f) :
    Integrable (fun p : ℝ × ℝ => (positivePinchingDensity B Y p : ℂ) * f p) volume := by
  have hν := positivePinching_continuous_integrable hB hB2 hY hf
  change Integrable f (volume.withDensity
    (fun p => ENNReal.ofReal (positivePinchingDensity B Y p))) at hν
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_positivePinchingDensity B Y).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hν
  simpa only [ENNReal.toReal_ofReal (positivePinching_density_nonneg B Y _),
    Complex.real_smul] using h

theorem positivePinching_diagonal_weighted_moment
    (σ : ι → Bool) {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (m : ℕ) {g : ℝ → ℂ} (hg : Continuous g) :
    (∫ p : ℝ × ℝ, g p.1 * (p.2 : ℂ) ^ m
      ∂positivePinchingMeasure (involutionFromSigns σ) Y) =
      ∫ x in (-1 : ℝ)..1, g x * pinchingCycleMoment σ Y m x := by
  have hB := involutionFromSigns_isHermitian σ
  have hB2 := involutionFromSigns_sq σ
  have hc : Continuous (fun p : ℝ × ℝ => g p.1 * (p.2 : ℂ) ^ m) := by
    exact (hg.comp continuous_fst).mul ((Complex.continuous_ofReal.comp continuous_snd).pow m)
  have hint := positivePinching_continuous_density_product_integrable hB hB2 hY hc
  have hslices : (fun x : ℝ => ∫ y : ℝ,
      (positivePinchingDensity (involutionFromSigns σ) Y (x, y) : ℂ) *
        (g x * (y : ℂ) ^ m)) =
      (Ioo (-1 : ℝ) 1).indicator (fun x => g x * pinchingCycleMoment σ Y m x) := by
    funext x
    by_cases hx : x ∈ Ioo (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      have hfun : (fun y : ℝ =>
          (positivePinchingDensity (involutionFromSigns σ) Y (x, y) : ℂ) *
            (g x * (y : ℂ) ^ m)) =
          (fun y : ℝ => g x * ((y ^ m *
            positivePinchingDensity (involutionFromSigns σ) Y (x, y) : ℝ) : ℂ)) := by
        funext y
        push_cast
        ring
      rw [hfun, integral_const_mul, integral_complex_ofReal,
        positivePinching_diagonal_cycle_moment σ hY m hx]
    · simp only [positivePinchingDensity, if_neg hx, Complex.ofReal_zero, zero_mul,
        integral_zero, Set.indicator_of_notMem hx]
  rw [positivePinching_integral_eq_density_integral,
    Measure.volume_eq_prod ℝ ℝ,
    integral_prod _ hint, hslices, integral_indicator measurableSet_Ioo,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]

end
end CGLMPBounds.Hardy
