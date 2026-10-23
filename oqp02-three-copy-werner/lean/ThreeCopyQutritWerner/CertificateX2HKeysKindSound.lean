module

public import ThreeCopyQutritWerner.CertificateX2HKeysKind

@[expose] public section


/-!
# Soundness of the per-key kind check

`kindCheck_sound`: if `kindCheck b = true` then the kind projector of `b` fixes its image and,
for standard keys, the swap of the first two slots fixes it (frame-coordinate mirrors).
-/

set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner.X2Sites

open X2

/-- The three components of a type triple. -/
def tcomp (τ : Fin 7 × Fin 7 × Fin 7) : Fin 3 → Fin 7 := ![τ.1, τ.2.1, τ.2.2]

theorem x2hCoords_lt (τ : Fin 7 × Fin 7 × Fin 7) (i : HIdx τ) (k : Fin 3) :
    x2hCoords τ i k < hsz (tcomp τ k) := by
  have hi : (i : ℕ) < hsz τ.1 * (hsz τ.2.1 * hsz τ.2.2) := i.isLt
  have hpos : 0 < hsz τ.2.1 * hsz τ.2.2 := hsz_pos τ i
  have hpos2 : 0 < hsz τ.2.2 := Nat.pos_of_mul_pos_left hpos
  rw [x2hCoords_apply]
  fin_cases k
  · show (i : ℕ) / (hsz τ.2.1 * hsz τ.2.2) < hsz τ.1
    rw [Nat.div_lt_iff_lt_mul hpos]
    exact hi
  · show (i : ℕ) % (hsz τ.2.1 * hsz τ.2.2) / hsz τ.2.2 < hsz τ.2.1
    rw [Nat.div_lt_iff_lt_mul hpos2]
    exact Nat.mod_lt _ hpos
  · show (i : ℕ) % (hsz τ.2.1 * hsz τ.2.2) % hsz τ.2.2 < hsz τ.2.2
    exact Nat.mod_lt _ hpos2

/-- Admissible slot permutation: it maps every slot to one of the same type. -/
theorem perm_bounds (τ : Fin 7 × Fin 7 × Fin 7) (p : Fin 6)
    (hτ : ∀ k, tcomp τ (x2Perm3 p k) = tcomp τ k) (i : HIdx τ) :
    (x2hCoords τ i ∘ x2Perm3 p) 0 < hsz τ.1 ∧ (x2hCoords τ i ∘ x2Perm3 p) 1 < hsz τ.2.1 ∧
      (x2hCoords τ i ∘ x2Perm3 p) 2 < hsz τ.2.2 := by
  have h := fun k => x2hCoords_lt τ i (x2Perm3 p k)
  refine ⟨?_, ?_, ?_⟩
  · have := h 0
    rw [hτ 0] at this
    exact this
  · have := h 1
    rw [hτ 1] at this
    exact this
  · have := h 2
    rw [hτ 2] at this
    exact this

/-- Row action of an admissible slot permutation on an h image, in kernel form. -/
theorem x2hImage_perm (b : x2Key 0) (p : Fin 6)
    (hτ : ∀ k, tcomp (x2hTau b) (x2Perm3 p k) = tcomp (x2hTau b) k)
    (i : HIdx (x2hTau b)) (c : x2Col 0 b) :
    (x2hSlotPerm (x2hTau b) p * x2hImage b) i c =
      ((jEntry2 (x2KeyGlobal 0 b) (hsz (x2hTau b).2.1 * hsz (x2hTau b).2.2)
        (pidxN (hsz (x2hTau b).2.1) (hsz (x2hTau b).2.2) i p) c : ℤ) : ℂ) := by
  obtain ⟨h0, h1, h2⟩ := perm_bounds _ p hτ i
  rw [x2h_slotPerm_mul _ p _ i c h0 h1 h2]
  simp only [x2hImage, Matrix.of_apply]
  rw [jEntry2_eq _ _ _ _ (hsz_pos _ i)]
  congr 3

/-! ## Admissibility in the three patterns -/

theorem adm_triple (τ : Fin 7 × Fin 7 × Fin 7) (h : τ.1 = τ.2.1 ∧ τ.2.1 = τ.2.2) (p : Fin 6) :
    ∀ k, tcomp τ (x2Perm3 p k) = tcomp τ k := by
  obtain ⟨h1, h2⟩ := h
  intro k
  have hall : ∀ k', tcomp τ k' = τ.1 := by
    intro k'
    fin_cases k'
    · rfl
    · exact h1.symm
    · exact (h1.trans h2).symm
  rw [hall, hall]

theorem adm_pair01 (τ : Fin 7 × Fin 7 × Fin 7) (h : τ.1 = τ.2.1) :
    ∀ k, tcomp τ (x2Perm3 x2Swap01Idx k) = tcomp τ k := by
  intro k
  fin_cases k
  · exact h.symm
  · exact h
  · rfl

theorem adm_pair12 (τ : Fin 7 × Fin 7 × Fin 7) (h : τ.2.1 = τ.2.2) :
    ∀ k, tcomp τ (x2Perm3 x2Swap12Idx k) = tcomp τ k := by
  intro k
  fin_cases k
  · rfl
  · exact h.symm
  · exact h

/-! ## The check gives entry identities -/

theorem allIC_int {n r : ℕ} {f : ℕ → ℕ → ℤ} {g : ℕ → ℕ → ℤ}
    (h : allIC n r (fun i c => f i c == g i c) = true) (i c : ℕ) (hi : i < n) (hc : c < r) :
    f i c = g i c := by
  have := allIC_spec n r _ h i c hi hc
  exact beq_iff_eq.mp this

/-! ## Soundness -/

/-- Entry identity of one admissible permutation, from a passing per-entry check. -/
theorem perm_entry (b : x2Key 0) (p : Fin 6)
    (hτ : ∀ k, tcomp (x2hTau b) (x2Perm3 p k) = tcomp (x2hTau b) k) (s : ℤ)
    (h : allIC (hsz (x2hTau b).1 * (hsz (x2hTau b).2.1 * hsz (x2hTau b).2.2)) (x2KeySize 0 b)
      (fun i c => jEntry2 (x2KeyGlobal 0 b) (hsz (x2hTau b).2.1 * hsz (x2hTau b).2.2)
        (pidxN (hsz (x2hTau b).2.1) (hsz (x2hTau b).2.2) i p) c ==
          s * jEntry2 (x2KeyGlobal 0 b) (hsz (x2hTau b).2.1 * hsz (x2hTau b).2.2) i c) = true)
    (i : HIdx (x2hTau b)) (c : x2Col 0 b) :
    (x2hSlotPerm (x2hTau b) p * x2hImage b) i c = (s : ℂ) * x2hImage b i c := by
  rw [x2hImage_perm b p hτ i c, x2hImage_apply, allIC_int h i c i.isLt c.isLt]
  push_cast
  ring

theorem kindCheck_sound (b : x2Key 0) (hchk : kindCheck b = true) :
    x2hKindProj (x2hTau b) (x2KeyKind 0 b) * x2hImage b = x2hImage b ∧
      (x2KeyDegree 0 b = 2 → x2hSlotPerm (x2hTau b) x2Swap01Idx * x2hImage b = x2hImage b) := by
  unfold kindCheck at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨hk, hs⟩ := hchk
  constructor
  · unfold x2hKindProj
    simp only []
    by_cases h3 : (x2hTau b).1 = (x2hTau b).2.1 ∧ (x2hTau b).2.1 = (x2hTau b).2.2
    · rw [if_pos h3] at hk ⊢
      by_cases hk0 : x2KeyKind 0 b = 0
      · rw [if_pos hk0] at hk ⊢
        have he : ∀ (p : Fin 6) (i : HIdx (x2hTau b)) (c : x2Col 0 b),
            (x2hSlotPerm (x2hTau b) p * x2hImage b) i c = x2hImage b i c := by
          intro p i c
          rw [x2hImage_perm b p (adm_triple _ h3 p) i c, x2hImage_apply]
          have hall := allIC_spec _ _ _ hk i c i.isLt c.isLt
          have := List.all_eq_true.mp hall p (List.mem_finRange p)
          rw [beq_iff_eq.mp this]
        ext i c
        rw [Matrix.smul_mul, Matrix.sum_mul, Matrix.smul_apply, Matrix.sum_apply]
        simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
        push_cast
        ring
      · rw [if_neg hk0] at hk ⊢
        by_cases hk1 : x2KeyKind 0 b = 1
        · rw [if_pos hk1] at hk ⊢
          have he : ∀ (p : Fin 6) (i : HIdx (x2hTau b)) (c : x2Col 0 b),
              (x2hSlotPerm (x2hTau b) p * x2hImage b) i c =
                ((x2Perm3Sign p : ℚ) : ℂ) * x2hImage b i c := by
            intro p i c
            rw [x2hImage_perm b p (adm_triple _ h3 p) i c, x2hImage_apply]
            have hall := allIC_spec _ _ _ hk i c i.isLt c.isLt
            have := beq_iff_eq.mp (List.all_eq_true.mp hall p (List.mem_finRange p))
            rw [this]
            fin_cases p <;> norm_num [x2Perm3Sign]
          ext i c
          rw [Matrix.smul_mul, Matrix.sum_mul, Matrix.smul_apply, Matrix.sum_apply]
          simp only [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, he, Fin.sum_univ_six, x2Perm3Sign]
          norm_num
          ring
        · rw [if_neg hk1] at hk ⊢
          ext i c
          have he := allIC_int hk i c i.isLt c.isLt
          have h0 := x2hImage_perm b 0 (adm_triple _ h3 0) i c
          have h3' := x2hImage_perm b 3 (adm_triple _ h3 3) i c
          have h4 := x2hImage_perm b 4 (adm_triple _ h3 4) i c
          have h1 := x2hImage_perm b 1 (adm_triple _ h3 1) i c
          have h2 := x2hImage_perm b 2 (adm_triple _ h3 2) i c
          have h5 := x2hImage_perm b 5 (adm_triple _ h3 5) i c
          have he' : (x2hSlotPerm (x2hTau b) 0 * x2hImage b) i c + (x2hSlotPerm (x2hTau b) 3 * x2hImage b) i c +
              (x2hSlotPerm (x2hTau b) 4 * x2hImage b) i c = 0 := by
            rw [h0, h3', h4]
            exact_mod_cast he
          rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.sub_apply]
          rw [Matrix.smul_mul, Matrix.sum_mul, Matrix.smul_apply, Matrix.sum_apply]
          rw [Matrix.smul_mul, Matrix.sum_mul, Matrix.smul_apply, Matrix.sum_apply]
          simp only [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_six, x2Perm3Sign]
          norm_num
          linear_combination (-(1 : ℂ) / 3) * he'
    · rw [if_neg h3] at hk ⊢
      by_cases h01 : (x2hTau b).1 = (x2hTau b).2.1
      · rw [if_pos h01] at hk ⊢
        ext i c
        have he : (x2hSlotPerm (x2hTau b) x2Swap01Idx * x2hImage b) i c =
            ((if x2KeyKind 0 b = 0 then (1 : ℤ) else -1 : ℤ) : ℂ) * x2hImage b i c := by
          apply perm_entry b x2Swap01Idx (adm_pair01 _ h01)
          by_cases hk0 : x2KeyKind 0 b = 0
          · simp only [hk0, if_true, one_mul] at hk ⊢
            exact hk
          · simp only [hk0, if_false] at hk ⊢
            simpa [neg_one_mul] using hk
        rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_apply,
          Matrix.add_apply, Matrix.smul_apply, he]
        split_ifs <;> push_cast <;> ring
      · rw [if_neg h01] at hk ⊢
        by_cases h12 : (x2hTau b).2.1 = (x2hTau b).2.2
        · rw [if_pos h12] at hk ⊢
          ext i c
          have he : (x2hSlotPerm (x2hTau b) x2Swap12Idx * x2hImage b) i c =
              ((if x2KeyKind 0 b = 0 then (1 : ℤ) else -1 : ℤ) : ℂ) * x2hImage b i c := by
            apply perm_entry b x2Swap12Idx (adm_pair12 _ h12)
            by_cases hk0 : x2KeyKind 0 b = 0
            · simp only [hk0, if_true, one_mul] at hk ⊢
              exact hk
            · simp only [hk0, if_false] at hk ⊢
              simpa [neg_one_mul] using hk
          rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_apply,
            Matrix.add_apply, Matrix.smul_apply, he]
          split_ifs <;> push_cast <;> ring
        · rw [if_neg h12]
          exact Matrix.one_mul _
  · intro hdeg
    rw [if_pos hdeg] at hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨h01, hs⟩ := hs
    ext i c
    have := perm_entry b x2Swap01Idx (adm_pair01 _ h01) 1 (by simpa using hs) i c
    rw [this]
    push_cast
    ring

end ThreeCopyQutritWerner.X2Sites
