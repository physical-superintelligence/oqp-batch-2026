module

public import CGLMPBounds.Partition.MatrixFourierSummability
public import CGLMPBounds.Partition.CircularBranch
public import CGLMPBounds.Partition.ConsecutiveBasics

@[expose] public section


/-! Literal D.2 negative Fourier convergence for consecutive and circular
assignments, supplied by actual bounded measurable branches and Parseval.
The pair-kernel equality and Hardy lower bound remain separate. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise
noncomputable section

theorem consecutivePartitionBranch_norm_le {d r : ℕ} (ℓ : ConsecutivePartition d)
    (V : Fin d → Circulation.Mat r) (t : ℝ) :
    ‖consecutivePartitionBranch ℓ V t‖ ≤ ∑ j, ‖V j‖ := by
  simp only [consecutivePartitionBranch, norm_smul, Matrix.norm_conjTranspose]
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, Real.exp_zero, one_mul]
  unfold consecutivePartitionStep
  calc
    _ ≤ ∑ j, ‖(ℓ.cell j).indicator (fun _ => V j) t‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases ht : t ∈ ℓ.cell j <;> simp [Set.indicator_apply, ht]

theorem consecutivePartitionBranch_fourier_summable {d r : ℕ} (ℓ : ConsecutivePartition d)
    (V : Fin d → Circulation.Mat r) :
    Summable (fun n => Circulation.hsSq
      (matrixNegativeFourierCoefficient (consecutivePartitionBranch ℓ V) n)) := by
  have hU : Measurable (consecutivePartitionBranch ℓ V) := by
    have hs := measurable_consecutivePartitionStep ℓ V
    unfold consecutivePartitionBranch
    fun_prop
  exact matrixNegativeFourierEnergy_summable_of_bounded _ hU (∑ j, ‖V j‖)
    (consecutivePartitionBranch_norm_le ℓ V)

theorem circularAssignmentBranch_norm_le {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (a : Fin d) (T : Fin d → ℝ) (t : ℝ) :
    ‖circularAssignmentBranch hd V a T t‖ ≤ ∑ j, ‖V j‖ := by
  simp only [circularAssignmentBranch, norm_smul, Matrix.norm_conjTranspose]
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, Real.exp_zero, one_mul]
  simp only [circularAssignmentStep, norm_smul, norm_pow, norm_neg, Complex.norm_I,
    one_pow, one_mul]
  exact Finset.single_le_sum (fun j _ => norm_nonneg (V j)) (Finset.mem_univ _)

theorem circularAssignmentBranch_fourier_summable {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (a : Fin d) (T : Fin d → ℝ) :
    Summable (fun n => Circulation.hsSq
      (matrixNegativeFourierCoefficient (circularAssignmentBranch hd V a T) n)) := by
  have hU : Measurable (circularAssignmentBranch hd V a T) := by
    have hpair : Measurable (fun t : ℝ => (T, t)) :=
      measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using
      (measurable_circularAssignmentBranch_joint hd V a).comp hpair
  exact matrixNegativeFourierEnergy_summable_of_bounded _ hU (∑ j, ‖V j‖)
    (circularAssignmentBranch_norm_le hd V a T)

end
end CGLMPBounds.Partition
