module

public import CGLMPBounds.Partition.BoundaryBasics

@[expose] public section


/-! Exact circular-arc geometry used by D.2's cyclic averaging. These
identities are pointwise, including repeated boundaries. -/

namespace CGLMPBounds.Partition
open Set
noncomputable section

theorem fract_sub_lt_iff {s t u : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    Int.fract (u - s) < t - s ↔ s ≤ Int.fract u ∧ Int.fract u < t := by
  rw [← Int.fract_fract_sub u s]
  by_cases hu : s ≤ Int.fract u
  · rw [Int.fract_eq_self.mpr ⟨sub_nonneg.mpr hu,
      by linarith [Int.fract_lt_one u]⟩]
    constructor
    · intro h
      exact ⟨hu, by linarith⟩
    · intro h
      linarith [h.2]
  · have hu' : Int.fract u < s := lt_of_not_ge hu
    have he : Int.fract (Int.fract u - s) = Int.fract u - s + 1 := by
      rw [← Int.fract_add_one (Int.fract u - s)]
      exact Int.fract_eq_self.mpr ⟨by linarith [Int.fract_nonneg u], by linarith⟩
    rw [he]
    constructor
    · intro h
      exfalso
      linarith [Int.fract_nonneg u]
    · intro h
      exact (hu h.1).elim

theorem boundaryArcCount_add_initial (d : ℕ) (T : Fin d → ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    boundaryArcCount d s (t - s) T + boundaryArcCount d 0 s T =
      boundaryArcCount d 0 t T := by
  classical
  let A : Finset (Fin d) := Finset.univ.filter (fun j => Int.fract (T j) < t)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := A) (fun j => s ≤ Int.fract (T j))
  have hleft : A.filter (fun j => s ≤ Int.fract (T j)) =
      Finset.univ.filter (fun j => Int.fract (T j - s) < t - s) := by
    ext j
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and,
      fract_sub_lt_iff hs hst ht]
    exact and_comm
  have hright : A.filter (fun j => ¬s ≤ Int.fract (T j)) =
      Finset.univ.filter (fun j => Int.fract (T j) < s) := by
    ext j
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    constructor
    · exact And.right
    · intro h
      exact ⟨h.trans_le hst, h⟩
  rw [hleft, hright] at hsplit
  simpa only [boundaryArcCount, sub_zero, A] using hsplit

end
end CGLMPBounds.Partition
