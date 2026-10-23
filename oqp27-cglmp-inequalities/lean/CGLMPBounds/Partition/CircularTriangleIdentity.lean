module

public import CGLMPBounds.Partition.CircularHardyPairIdentity
public import CGLMPBounds.Partition.StepPairIntegral

@[expose] public section


/-! Literal circular D.2 identity on the upper triangle, with actual
integrability proved from the boundary geometry. This is still prior to
the random-boundary Fubini and D.3 coefficient calculation. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix
noncomputable section

theorem circularAssignmentStep_pair_integrable {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (V : Fin d → Circulation.Mat r) (hV : ∀ j, (V j)ᴴ * V j = 1)
    (a : Fin d) (T : Fin d → ℝ) :
    Integrable (stepPairIntegrand (circularAssignmentStep hd V a T))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  obtain ⟨m, ℓ, W, hW, hcell⟩ :=
    circularAssignmentStep_consecutive_representation hd V hV a T
  exact (stepPairIntegrand_integrable_and_eq_pairForm hr ℓ W hW _ hcell).1

theorem circularAssignmentBranch_hardyGap_eq_triangle {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (V : Fin d → Circulation.Mat r) (hV : ∀ j, (V j)ᴴ * V j = 1)
    (a : Fin d) (T : Fin d → ℝ) :
    matrixNegativeFourierEnergy (circularAssignmentBranch hd V a T) -
      sourceFourthRootHardyConstant =
      (1 / 2 : ℝ) * ∫ p : ℝ × ℝ, stepPairIntegrand (circularAssignmentStep hd V a T) p
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  obtain ⟨m, ℓ, W, hW, hcell, he⟩ :=
    circularAssignmentBranch_exists_pair_identity hd hr V hV a T
  exact he.trans (stepPairIntegrand_integrable_and_eq_pairForm hr ℓ W hW _ hcell).2.symm

end
end CGLMPBounds.Partition
