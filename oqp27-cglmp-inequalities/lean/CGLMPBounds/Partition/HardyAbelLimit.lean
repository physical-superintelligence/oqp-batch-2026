module

public import CGLMPBounds.Partition.BranchFourierSummability
public import Mathlib.Analysis.Complex.AbelLimit

@[expose] public section


/-! Abel regularization of the actual matrix negative Fourier energy.
Mathlib's real Abel theorem applies to the already derived coefficient
summability. -/

namespace CGLMPBounds.Partition
open Filter
open scoped Topology
noncomputable section

theorem consecutivePartitionHardyEnergy_abel_limit {d r : ℕ}
    (ℓ : ConsecutivePartition d) (V : Fin d → Circulation.Mat r) :
    Tendsto (fun q : ℝ => ∑' n : ℕ,
      Circulation.hsSq (matrixNegativeFourierCoefficient (consecutivePartitionBranch ℓ V) n) * q ^ n)
      (𝓝[<] (1 : ℝ))
      (𝓝 (matrixNegativeFourierEnergy (consecutivePartitionBranch ℓ V))) := by
  exact Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (consecutivePartitionBranch_fourier_summable ℓ V).hasSum.tendsto_sum_nat

theorem circularPartitionHardyEnergy_abel_limit {d r : ℕ}
    (hd : 0 < d) (V : Fin d → Circulation.Mat r) (a : Fin d) (T : Fin d → ℝ) :
    Tendsto (fun q : ℝ => ∑' n : ℕ,
      Circulation.hsSq (matrixNegativeFourierCoefficient (circularAssignmentBranch hd V a T) n) * q ^ n)
      (𝓝[<] (1 : ℝ))
      (𝓝 (matrixNegativeFourierEnergy (circularAssignmentBranch hd V a T))) := by
  exact Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (circularAssignmentBranch_fourier_summable hd V a T).hasSum.tendsto_sum_nat

end
end CGLMPBounds.Partition
