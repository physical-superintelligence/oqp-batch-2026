module

public import CGLMPBounds.Defs.FourthRootCut
public import Mathlib.Data.Finset.Max

@[expose] public section


/-!
# The ordered scalar equality labels are exactly cuts

This proves the combinatorial assertion in (E.1). The hypothesis is the
literal allowed-label relation for each ordered pair; passage from matrices
to a common eigenbasis is a separate obligation.
-/

namespace CGLMPBounds.Circulation

theorem scalar_labels_are_cut {d : ℕ} [NeZero d] (v : Fin d → Fin 4)
    (h : ∀ i j, i < j → v j = v i ∨ v j = v i + 3) :
    ∃ a : Fin 4, ∃ j₀ : Fin d, v = fourthRootCutLabels a j₀ := by
  classical
  let a := v 0
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hbase (j : Fin d) : v j = a ∨ v j = a + 3 := by
    by_cases hj : j = 0
    · exact Or.inl (by subst j; rfl)
    · exact h 0 j ((Fin.pos_iff_ne_zero' j).mpr hj)
  let s : Finset (Fin d) := Finset.univ.filter (fun j => v j ≠ a)
  by_cases hs : s.Nonempty
  · let k : Fin d := s.min' hs
    have hk : v k ≠ a := (Finset.mem_filter.mp (s.min'_mem hs)).2
    have hkpos : 0 < k.val := by
      by_contra he
      have hk0 : k = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      exact hk (by simp only [hk0]; rfl)
    have hka : v k = a + 3 := (hbase k).resolve_left hk
    have hbefore (j : Fin d) (hj : j < k) : v j = a := by
      by_contra hja
      have hjmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hja⟩
      have hkj : k ≤ j := s.min'_le j hjmem
      exact (not_le_of_gt hj) hkj
    have hafter (j : Fin d) (hj : k ≤ j) : v j = a + 3 := by
      rcases eq_or_lt_of_le hj with hkj | hkj
      · simpa only [← hkj] using hka
      · rcases h k j hkj with he | he
        · exact he.trans hka
        · have hcases := hbase j
          rw [hka] at he
          have hbad : ∀ z : Fin 4, z + 3 + 3 ≠ z ∧ z + 3 + 3 ≠ z + 3 := by decide
          rcases hcases with hj0 | hj3
          · exact False.elim ((hbad a).1 (he.symm.trans hj0))
          · exact False.elim ((hbad a).2 (he.symm.trans hj3))
    let j₀ : Fin d := ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
    refine ⟨a, j₀, ?_⟩
    funext j
    unfold fourthRootCutLabels
    split_ifs with hj
    · exact hafter j (by change k.val ≤ j.val; change k.val - 1 < j.val at hj; omega)
    · exact hbefore j (by change j.val < k.val; change ¬ k.val - 1 < j.val at hj; omega)
  · let j₀ : Fin d := ⟨d - 1, by omega⟩
    refine ⟨a, j₀, ?_⟩
    funext j
    have hj : v j = a := by
      by_contra he
      exact hs ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
    have hlast : ¬ j₀ < j := by change ¬ d - 1 < j.val; have := j.isLt; omega
    simp only [fourthRootCutLabels, if_neg hlast, hj]

/-- Every literal cut obeys all of the forbidden-label constraints. -/
theorem cut_labels_allowed {d : ℕ} (a : Fin 4) (j₀ : Fin d) :
    ∀ i j, i < j → fourthRootCutLabels a j₀ j = fourthRootCutLabels a j₀ i ∨
      fourthRootCutLabels a j₀ j = fourthRootCutLabels a j₀ i + 3 := by
  intro i j hij
  by_cases hi : j₀ < i
  · have hj : j₀ < j := lt_trans hi hij
    simp only [fourthRootCutLabels, if_pos hi, if_pos hj, true_or]
  · by_cases hj : j₀ < j
    · simp only [fourthRootCutLabels, if_neg hi, if_pos hj, or_true]
    · simp only [fourthRootCutLabels, if_neg hi, if_neg hj, true_or]

end CGLMPBounds.Circulation
