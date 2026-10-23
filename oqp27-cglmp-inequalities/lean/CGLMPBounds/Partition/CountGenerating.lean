module

public import CGLMPBounds.Partition.CountGeneratingZero
public import CGLMPBounds.Partition.RotationMeasure

@[expose] public section


/-! The actual single-mode tilted count generating function for an arbitrary
real arc origin. This transports the origin-zero calculation by the proved
measure-preserving fractional-part rotation. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

lemma integrable_fourierBoundaryDensity_count_zero (d n : ℕ) (x : ℝ) (z : ℂ) :
    Integrable (fun T : Fin d → ℝ =>
      (fourierBoundaryDensity d n T : ℂ) * z ^ boundaryArcCount d 0 x T)
        (boundaryProductMeasure d) := by
  have hcont : Continuous (fun T => (fourierBoundaryDensity d n T : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_fourierBoundaryDensity d n)
  apply (integrable_boundaryArcCount_zero_pow d x z).bdd_mul (c := (d : ℝ))
    hcont.aestronglyMeasurable
  filter_upwards [] with T
  rw [Complex.norm_real, Real.norm_of_nonneg (fourierBoundaryDensity_nonneg d n T)]
  exact fourierBoundaryDensity_le d n T

/-- The exact source single Fourier-power count polynomial, for the actual
uniform boundary points, density, and fractional-part arc count. -/
theorem fourierBoundaryDensity_count_generating (d n : ℕ)
    (hd : 2 ≤ d) (hn : 0 < n) (origin x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) :
    (∫ T, (fourierBoundaryDensity d n T : ℂ) * z ^ boundaryArcCount d origin x T
      ∂boundaryProductMeasure d) =
      (((1 - x : ℝ) : ℂ) + (x : ℂ) * z) ^ d +
        ((d : ℂ) - 1) * (fourierTiltShape n x : ℂ) * (z - 1) ^ 2 *
          (((1 - x : ℝ) : ℂ) + (x : ℂ) * z) ^ (d - 2) := by
  let G : (Fin d → ℝ) → ℂ := fun T =>
    (fourierBoundaryDensity d n T : ℂ) * z ^ boundaryArcCount d 0 x T
  have hrot := rotateBoundaryPoints_measurePreserving d origin
  have hG : AEStronglyMeasurable G (Measure.map (rotateBoundaryPoints d origin)
      (boundaryProductMeasure d)) := by
    rw [hrot.map_eq]
    exact (integrable_fourierBoundaryDensity_count_zero d n x z).aestronglyMeasurable
  have hmap := integral_map hrot.measurable.aemeasurable hG
  rw [hrot.map_eq] at hmap
  calc
    _ = ∫ T : Fin d → ℝ, G (rotateBoundaryPoints d origin T) ∂boundaryProductMeasure d := by
      apply integral_congr_ae
      filter_upwards [] with T
      simp only [G, fourierBoundaryDensity_rotate, boundaryArcCount_rotate]
    _ = ∫ T : Fin d → ℝ, G T ∂boundaryProductMeasure d := hmap.symm
    _ = _ := fourierBoundaryDensity_count_generating_zero d n hd hn x hx z

end
end CGLMPBounds.Partition
