module

public import CGLMPBounds.Partition.CircularBranch

@[expose] public section


/-! The genuine C.6 statement discharges all hypotheses needed for the
actual circular gap. This internal adapter takes C.6 as the explicit input
`hC6`. -/

namespace CGLMPBounds.Partition
open MeasureTheory
open scoped Matrix
noncomputable section

set_option maxHeartbeats 1000000 in
theorem circularPartitionHardyAverage_nonneg_of_matrixHardy_input {d r : ℕ}
    (hd : 0 < d) (hr : 0 < r)
    (hC6 : ∀ (U : ℝ → Circulation.Mat r),
      AEStronglyMeasurable U (volume.restrict (Set.Ioc (0 : ℝ) 1)) →
      (∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), (U t)ᴴ * U t = 1) →
      (∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
        U t ^ 4 = Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I) •
          (1 : Circulation.Mat r)) →
      sourceFourthRootHardyConstant ≤ matrixNegativeFourierEnergy U)
    (V : Fin d → Circulation.Mat r) (hunit : ∀ j, (V j)ᴴ * V j = 1)
    (hfour : ∀ j, V j ^ 4 = 1) (T : Fin d → ℝ) :
    0 ≤ circularPartitionHardyAverage hd V T := by
  letI : TopologicalSpace.PseudoMetrizableSpace (Circulation.Mat r) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin r → Fin r → ℂ))
  letI : SecondCountableTopology (Circulation.Mat r) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))
  have hterm (a : Fin d) : sourceFourthRootHardyConstant ≤
      matrixNegativeFourierEnergy (circularAssignmentBranch hd V a T) := by
    apply hC6
    · have hpair : Measurable (fun t : ℝ => (T, t)) :=
        measurable_const.prodMk measurable_id
      have hm : Measurable (circularAssignmentBranch hd V a T) :=
        (measurable_circularAssignmentBranch_joint hd V a).comp
          hpair
      exact hm.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (circularAssignmentBranch_unitary hd V hunit a T)
    · exact Filter.Eventually.of_forall (circularAssignmentBranch_fourth hd V hfour a T)
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun a _ => sub_nonneg.mpr (hterm a)))

end
end CGLMPBounds.Partition
