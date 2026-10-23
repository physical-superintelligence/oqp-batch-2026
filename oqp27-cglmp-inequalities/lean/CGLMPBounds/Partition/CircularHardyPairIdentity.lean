module

public import CGLMPBounds.Partition.CircularConsecutiveGeometry
public import CGLMPBounds.Partition.ConsecutiveHardyPairIdentity

@[expose] public section


/-! Transfer of the actual D.2 Fourier identity to the literal circular
assignment. A real consecutive partition is constructed from its actual
boundary points; no circular Hardy identity is assumed. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise
noncomputable section

lemma circularAssignmentBranch_coefficient_of_cells {d m r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (a : Fin d) (T : Fin d → ℝ)
    (ℓ : ConsecutivePartition m) (W : Fin m → Circulation.Mat r)
    (hcell : ∀ j : Fin m, ∀ t ∈ Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ),
      circularAssignmentStep hd V a T t = W j) (n : ℕ) :
    matrixNegativeFourierCoefficient (circularAssignmentBranch hd V a T) n =
      matrixNegativeFourierCoefficient (consecutivePartitionBranch ℓ W) n := by
  letI : ENormedAddMonoid (Circulation.Mat r) :=
    inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))
  let F : ℝ → Circulation.Mat r := fun t =>
    Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) •
      circularAssignmentBranch hd V a T t
  let G : ℝ → ℂ := fun t =>
    Complex.exp ((((Real.pi / 2 * (4 * (n : ℝ) + 3) * t : ℝ) : ℂ)) * Complex.I)
  have hb (j : Fin m) : ℓ.boundary j.castSucc ≤ ℓ.boundary j.succ :=
    ℓ.monotone_boundary (by change j.val ≤ j.val + 1; omega)
  have he (j : Fin m) : EqOn (fun t => G t • (W j)ᴴ) F
      (uIoo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ)) := by
    rw [uIoo_of_le (hb j)]
    intro t ht
    dsimp only [F, G]
    rw [circularAssignmentBranch, hcell j t ht, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hi (j : Fin m) :
      IntervalIntegrable F volume (ℓ.boundary j.castSucc) (ℓ.boundary j.succ) := by
    have hc : Continuous (fun t => G t • (W j)ᴴ) := by
      dsimp [G]
      fun_prop
    exact (hc.intervalIntegrable (ℓ.boundary j.castSucc)
      (ℓ.boundary j.succ)).congr_uIoo (he j)
  change (∫ t in (0 : ℝ)..1, F t) = _
  rw [← ℓ.sum_cell_integrals F hi, consecutivePartitionBranch_negative_coefficient]
  apply Finset.sum_congr rfl
  intro j _
  rw [← intervalIntegral.integral_congr_uIoo (he j), intervalIntegral.integral_smul_const]

/-- Every literal circular assignment has an actual consecutive unitary
representation and its actual negative Fourier energy has the D.2 pair
integral. This is an equality, without a Hardy positivity premise. -/
theorem circularAssignmentBranch_exists_pair_identity {d r : ℕ}
    (hd : 0 < d) (hr : 0 < r)
    (V : Fin d → Circulation.Mat r) (hV : ∀ j, (V j)ᴴ * V j = 1)
    (a : Fin d) (T : Fin d → ℝ) :
    ∃ (m : ℕ) (ℓ : ConsecutivePartition m) (W : Fin m → Circulation.Mat r),
      (∀ j, (W j)ᴴ * W j = 1) ∧
      (∀ j : Fin m, ∀ t ∈ Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ),
        circularAssignmentStep hd V a T t = W j) ∧
      matrixNegativeFourierEnergy (circularAssignmentBranch hd V a T) -
        sourceFourthRootHardyConstant = consecutivePartitionPairForm ℓ W := by
  obtain ⟨m, ℓ, W, hW, hcell⟩ :=
    circularAssignmentStep_consecutive_representation hd V hV a T
  refine ⟨m, ℓ, W, hW, hcell, ?_⟩
  have he : matrixNegativeFourierEnergy (circularAssignmentBranch hd V a T) =
      matrixNegativeFourierEnergy (consecutivePartitionBranch ℓ W) := by
    unfold matrixNegativeFourierEnergy
    apply tsum_congr
    intro n
    rw [circularAssignmentBranch_coefficient_of_cells hd V a T ℓ W hcell n]
  rw [he]
  exact consecutivePartitionHardyGap_eq_pairForm hr ℓ W hW

end
end CGLMPBounds.Partition
