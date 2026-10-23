module

public import CGLMPBounds.Partition.ConsecutiveBasics
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section


/-! Exact finite measure decomposition of [0,1] and its square into the
actual cells of a consecutive partition. Endpoints have Lebesgue measure
zero; repeated boundaries simply contribute the zero measure. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
noncomputable section

private lemma sum_restrict_adjacent_Ioc (μ : Measure ℝ) (b : ℕ → ℝ)
    (hb : Monotone b) (n : ℕ) :
    (∑ k ∈ Finset.range n, μ.restrict (Ioc (b k) (b (k + 1)))) =
      μ.restrict (Ioc (b 0) (b n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, ← Measure.restrict_union]
    · rw [Ioc_union_Ioc_eq_Ioc (hb (Nat.zero_le n)) (hb (Nat.le_succ n))]
    · apply Set.disjoint_left.mpr
      intro x hx hy
      exact (not_lt_of_ge hx.2) hy.1
    · exact measurableSet_Ioc

theorem ConsecutivePartition.sum_cell_measures {d : ℕ} (ℓ : ConsecutivePartition d) :
    (∑ j : Fin d, volume.restrict
      (Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ))) =
      volume.restrict (Ioo (0 : ℝ) 1) := by
  let b : ℕ → ℝ := fun n => ℓ.boundary ⟨min n d, Nat.lt_succ_iff.mpr (Nat.min_le_right n d)⟩
  have hb : Monotone b := by
    intro n k hnk
    apply ℓ.monotone_boundary
    exact min_le_min_right d hnk
  have hb₀ : b 0 = 0 := by simpa [b] using ℓ.boundary_zero
  have hbd : b d = 1 := by simpa [b, Fin.last] using ℓ.boundary_one
  have hbj (j : Fin d) : b j.val = ℓ.boundary j.castSucc := by
    simp only [b, Nat.min_eq_left j.isLt.le]
    rfl
  have hbjs (j : Fin d) : b (j.val + 1) = ℓ.boundary j.succ := by
    simp only [b, Nat.min_eq_left (Nat.succ_le_of_lt j.isLt)]
    rfl
  have he := sum_restrict_adjacent_Ioc volume b hb d
  rw [Finset.sum_range, hb₀, hbd] at he
  simpa only [hbj, hbjs, restrict_Ioo_eq_restrict_Ioc] using he

theorem ConsecutivePartition.sum_cell_product_measures {d : ℕ} (ℓ : ConsecutivePartition d) :
    (∑ j : Fin d, ∑ k : Fin d,
      (volume.restrict (Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ))).prod
        (volume.restrict (Ioo (ℓ.boundary k.castSucc) (ℓ.boundary k.succ)))) =
      (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)) := by
  let μ : Fin d → Measure ℝ := fun j =>
    volume.restrict (Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ))
  have hm : Measure.sum μ = volume.restrict (Ioo (0 : ℝ) 1) := by
    rw [Measure.sum_fintype]
    exact ℓ.sum_cell_measures
  have he := Measure.prod_sum μ μ
  rw [hm] at he
  rw [Measure.sum_fintype, Fintype.sum_prod_type] at he
  exact he.symm

end
end CGLMPBounds.Partition
