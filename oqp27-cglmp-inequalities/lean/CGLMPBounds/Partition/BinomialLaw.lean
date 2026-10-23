module

public import CGLMPBounds.Partition.CountLaw

@[expose] public section


/-! The actual unweighted binomial arc-count law at arbitrary origin,
including empty products and every natural count value. -/

namespace CGLMPBounds.Partition
open MeasureTheory Polynomial
noncomputable section

theorem boundaryArcCount_generating (d : ℕ) (origin x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) :
    (∫ T : Fin d → ℝ, z ^ boundaryArcCount d origin x T ∂boundaryProductMeasure d) =
      (1 - (x : ℂ) + (x : ℂ) * z) ^ d := by
  let G : (Fin d → ℝ) → ℂ := fun T => z ^ boundaryArcCount d 0 x T
  have hrot := rotateBoundaryPoints_measurePreserving d origin
  have hG : AEStronglyMeasurable G (Measure.map (rotateBoundaryPoints d origin)
      (boundaryProductMeasure d)) := by
    rw [hrot.map_eq]
    exact (integrable_boundaryArcCount_zero_pow d x z).aestronglyMeasurable
  have hmap := integral_map hrot.measurable.aemeasurable hG
  rw [hrot.map_eq] at hmap
  calc
    _ = ∫ T : Fin d → ℝ, G (rotateBoundaryPoints d origin T) ∂boundaryProductMeasure d := by
      apply integral_congr_ae
      filter_upwards [] with T
      simp only [G, boundaryArcCount_rotate]
    _ = ∫ T : Fin d → ℝ, G T ∂boundaryProductMeasure d := hmap.symm
    _ = _ := integral_boundaryArcCount_zero_pow d x hx z

theorem finiteCountPolynomial_boundaryProductMeasure (d : ℕ) (origin x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    finiteCountPolynomial (boundaryProductMeasure d) (boundaryArcCount d origin x) d =
      boundaryBinomialPolynomial d x := by
  apply Polynomial.funext
  intro z
  rw [finiteCountPolynomial_eval _ _ _ (measurable_boundaryArcCount d origin x)
    (boundaryArcCount_le d origin x), boundaryArcCount_generating d origin x hx z]
  simp [boundaryBinomialPolynomial]

theorem boundaryArcCount_binomial (d h : ℕ) (origin x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (boundaryProductMeasure d).real {T | boundaryArcCount d origin x T = h} =
      scalarBinomialWeight d h x := by
  apply Complex.ofReal_injective
  rw [← finiteCountPolynomial_coeff _ _ d h (boundaryArcCount_le d origin x),
    finiteCountPolynomial_boundaryProductMeasure d origin x hx,
    boundaryBinomialPolynomial_coeff]

end
end CGLMPBounds.Partition
