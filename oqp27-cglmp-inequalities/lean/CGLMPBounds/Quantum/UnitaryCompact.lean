module

public import CGLMPBounds.Quantum.StochasticVariance

@[expose] public section


/-! Compactness of the actual finite complex matrix unitary group in its
entry topology. The proof uses the literal column norm identity and the
compact product of closed unit discs, with no operator-norm convention. -/

namespace CGLMPBounds
noncomputable section
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma unitary_entry_norm_le_one (U : Matrix.unitaryGroup ι ℂ) (i j : ι) :
    ‖(U : Matrix ι ι ℂ) i j‖ ≤ 1 := by
  have h : Complex.normSq ((U : Matrix ι ι ℂ) i j) ≤
      ∑ a, Complex.normSq ((U : Matrix ι ι ℂ) a j) := by
    exact Finset.single_le_sum
      (f := fun a => Complex.normSq ((U : Matrix ι ι ℂ) a j))
      (fun a _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [unitary_weight_col_sum, Complex.normSq_eq_norm_sq] at h
  have hn := norm_nonneg ((U : Matrix ι ι ℂ) i j)
  nlinarith

theorem isCompact_matrix_unitaryGroup :
    IsCompact (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
  have hc : IsCompact ((Metric.closedBall (0 : ℂ) 1).matrix : Set (Matrix ι ι ℂ)) :=
    (isCompact_closedBall (0 : ℂ) 1).matrix
  apply hc.of_isClosed_subset isClosed_unitary
  intro U hU i j
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    unitary_entry_norm_le_one (⟨U, hU⟩ : Matrix.unitaryGroup ι ℂ) i j

end
end CGLMPBounds
