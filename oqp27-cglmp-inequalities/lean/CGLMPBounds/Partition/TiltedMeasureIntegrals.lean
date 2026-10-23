module

public import CGLMPBounds.Partition.CountGenerating

@[expose] public section


/-! Actual integrals under the literal Fourier-tilted probability measure.
This uses the defining withDensity measure, not a supplied count law. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

theorem integral_fourierBoundaryMeasure (d n : ℕ) (f : (Fin d → ℝ) → ℂ) :
    (∫ T, f T ∂fourierBoundaryMeasure d n) =
      ∫ T, (fourierBoundaryDensity d n T : ℂ) * f T ∂boundaryProductMeasure d := by
  have hm : Measurable (fun T => ENNReal.ofReal (fourierBoundaryDensity d n T)) :=
    (continuous_fourierBoundaryDensity d n).measurable.ennreal_ofReal
  have htop : ∀ᵐ T ∂boundaryProductMeasure d,
      ENNReal.ofReal (fourierBoundaryDensity d n T) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  unfold fourierBoundaryMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hm htop f]
  apply integral_congr_ae
  filter_upwards [] with T
  rw [ENNReal.toReal_ofReal (fourierBoundaryDensity_nonneg d n T), Complex.real_smul]

theorem fourierBoundaryMeasure_count_generating (d n : ℕ)
    (hd : 2 ≤ d) (hn : 0 < n) (origin x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) :
    (∫ T, z ^ boundaryArcCount d origin x T ∂fourierBoundaryMeasure d n) =
      (((1 - x : ℝ) : ℂ) + (x : ℂ) * z) ^ d +
        ((d : ℂ) - 1) * (fourierTiltShape n x : ℂ) * (z - 1) ^ 2 *
          (((1 - x : ℝ) : ℂ) + (x : ℂ) * z) ^ (d - 2) := by
  rw [integral_fourierBoundaryMeasure]
  exact fourierBoundaryDensity_count_generating d n hd hn origin x hx z

end
end CGLMPBounds.Partition
