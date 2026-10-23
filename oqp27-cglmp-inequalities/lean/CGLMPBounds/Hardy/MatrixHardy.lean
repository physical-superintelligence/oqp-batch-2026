module

public import CGLMPBounds.Hardy.FourthRootBoundaryMean
public import CGLMPBounds.Hardy.HardyMatrixPinchingInequality

@[expose] public section


/-! The literal general matrix Hardy bound (C.6).
Every analytic input is an actual theorem: fourfold Fourier transport,
Hilbert pairing, pinching, Poisson radial convergence and boundary mean.
There is no Hardy, positivity, mean-value or approximation premise. -/
namespace CGLMPBounds.Hardy
noncomputable section
open MeasureTheory
open scoped Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem fourth_root_matrix_Hardy_bound {r : ℕ} (hr : 0 < r)
    (U : ℝ → Circulation.Mat r)
    (hU : AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hunit : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ * U t = 1)
    (hfour : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      U t ^ 4 = Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I) •
        (1 : Circulation.Mat r)) :
    Partition.sourceFourthRootHardyConstant ≤ Partition.matrixNegativeFourierEnergy U := by
  letI : NeZero r := ⟨ne_of_gt hr⟩
  obtain ⟨hpair,hidentity⟩ := fourthRootCircle_hilbert_pairing hr U hU hunit hfour
  obtain ⟨hpinch,hpair_le⟩ := fourthRootCircle_hilbert_pinching_bound hr U hU hunit hfour
  obtain ⟨hpotential,hmean⟩ := fourthRootCircle_boundary_potential_mean hr U hU hunit hfour
  have hinv := (fourthRootCircle_involutions hr U hU hunit hfour).1
  have hB := (fourthRootCircle_parts_memLp U hU hunit).2
  have hHB := matrixHilbert_hermitian_ae (fourthRootCircleB U) hB
    (hinv.mono (fun _ h => h.2.1))
  have hpinch_le :
      (∫ t, normalizedMatrixAbsTrace
        (positivePinchingPart (fourthRootCircleB U t)
          (matrixHilbert (fourthRootCircleB U) t)) ∂circleMeasure) ≤
      ∫ t, matrixHardyPotential
        (fourthRootCircleB U t+Complex.I • matrixHilbert (fourthRootCircleB U) t)
          ∂circleMeasure := by
    apply integral_mono_ae hpinch hpotential
    filter_upwards [hinv,hHB] with t ht hHt
    exact hardyMatrix_boundary_pinching_inequality ht.2.1 ht.2.2.2.1 hHt
  have henergy : 1-2*Partition.matrixNegativeFourierEnergy U ≤ hardyStripCenterConstant := by
    rw [hidentity]
    exact hpair_le.trans (hmean ▸ hpinch_le)
  unfold Partition.sourceFourthRootHardyConstant
  unfold hardyStripCenterConstant at henergy
  have hscale : 8 * Partition.sourceCatalanConstant / Real.pi ^ 2 =
      2 * (4 * Partition.sourceCatalanConstant / Real.pi ^ 2) := by ring
  rw [hscale] at henergy
  linarith

end
end CGLMPBounds.Hardy
