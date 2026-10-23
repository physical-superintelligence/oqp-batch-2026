module

public import CGLMPBounds.Defs.ScalarForm
public import CGLMPBounds.Partition.SourceCoefficientMatching

@[expose] public section


/-! The exact D.8 coefficient-form decomposition, using the genuine source
count-probability coefficients. Identifying that coefficient form with the
averaged Hardy form remains a separate D.2 obligation. -/

namespace CGLMPBounds.Partition
noncomputable section

theorem scalarEdgeForm_source_decomposition {d r : ℕ} (hd : 2 ≤ d)
    (V : Fin d → Circulation.Mat r) (origin : ℝ) :
    scalarEdgeForm (fun h => scalarSecant ((h : ℝ) / d) / (2 * (d : ℝ) ^ 2)) V =
      scalarEdgeForm (fun h => sourcePartitionCoefficient d h origin) V +
        (1 / (2 * (d : ℝ) ^ 2)) *
          scalarEdgeForm (fun h => scalarIntegralError d h + scalarPartitionCoefficient d h) V := by
  simp only [scalarEdgeForm, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    have hh0 : 0 < j.val - i.val := Nat.sub_pos_of_lt hij
    have hhd : j.val - i.val < d := lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
    have hk0 : 0 < d - (j.val - i.val) := Nat.sub_pos_of_lt hhd
    have hkd : d - (j.val - i.val) < d := by omega
    rw [sourcePartitionCoefficient_error_decomposition d _ hh0 hhd origin,
      sourcePartitionCoefficient_error_decomposition d _ hk0 hkd origin]
    ring
  · simp [hij]

end
end CGLMPBounds.Partition
