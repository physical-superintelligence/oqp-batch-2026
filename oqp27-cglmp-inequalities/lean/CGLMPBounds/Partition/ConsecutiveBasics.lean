module

public import CGLMPBounds.Defs.PartitionHardy

@[expose] public section


/-! Geometry and measurable step functions for the literal D.2 partition.
No Hardy inequality or projection identity is assumed. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix
noncomputable section

lemma ConsecutivePartition.cell_disjoint {d : ℕ} (ℓ : ConsecutivePartition d)
    {j k : Fin d} (hjk : j ≠ k) : Disjoint (ℓ.cell j) (ℓ.cell k) := by
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · apply Set.disjoint_left.mpr
    intro t htj htk
    have hbk : ℓ.boundary j.succ ≤ ℓ.boundary k.castSucc :=
      ℓ.monotone_boundary (by exact_mod_cast (show j.val + 1 ≤ k.val from hlt))
    exact (not_lt_of_ge (le_trans hbk htk.1)) htj.2
  · apply Set.disjoint_left.mpr
    intro t htj htk
    have hbj : ℓ.boundary k.succ ≤ ℓ.boundary j.castSucc :=
      ℓ.monotone_boundary (by exact_mod_cast (show k.val + 1 ≤ j.val from hgt))
    exact (not_lt_of_ge (le_trans hbj htj.1)) htk.2

theorem consecutivePartitionStep_eq {d r : ℕ} (ℓ : ConsecutivePartition d)
    (V : Fin d → Circulation.Mat r) (j : Fin d) {t : ℝ} (ht : t ∈ ℓ.cell j) :
    consecutivePartitionStep ℓ V t = V j := by
  unfold consecutivePartitionStep
  rw [Finset.sum_eq_single j]
  · exact Set.indicator_of_mem ht _
  · intro k _ hkj
    apply Set.indicator_of_notMem
    exact fun htk => Set.disjoint_left.mp (ℓ.cell_disjoint hkj) htk ht
  · simp

theorem measurable_consecutivePartitionStep {d r : ℕ} (ℓ : ConsecutivePartition d)
    (V : Fin d → Circulation.Mat r) : Measurable (consecutivePartitionStep ℓ V) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro k
  simp only [consecutivePartitionStep, Matrix.sum_apply]
  apply Finset.measurable_sum
  intro j _
  have hcell : Measurable (fun t : ℝ => (ℓ.cell j).indicator (fun _ => V j i k) t) :=
    measurable_const.indicator measurableSet_Ico
  convert hcell using 1
  funext t
  by_cases ht : t ∈ ℓ.cell j <;> simp [ht]

theorem consecutivePartitionStep_fourth {d r : ℕ} (ℓ : ConsecutivePartition d)
    (V : Fin d → Circulation.Mat r) (hfour : ∀ j, V j ^ 4 = 1)
    (j : Fin d) {t : ℝ} (ht : t ∈ ℓ.cell j) :
    consecutivePartitionStep ℓ V t ^ 4 = 1 := by
  rw [consecutivePartitionStep_eq ℓ V j ht, hfour]

end
end CGLMPBounds.Partition
