module

public import ThreeCopyQutritWerner.CertificateX2CoreBatch

@[expose] public section


/-!
# Contraction core: per-output kernel checks for the batched chain

Generated check modules decide one small predicate per flat index `t = a m + o` (one output per
declaration for the axis-2 and axis-1 stages and the regrouping, a few outputs per declaration
for the axis-0 stage), so that the kernel's per-declaration caches stay small. These lemmas turn
the joined statements `∀ t < N m, Q (t / m) (t % m)` into the hypotheses of `x2ChainB`.
-/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

theorem x2b_unflat (N m : ℕ) (Q : ℕ → ℕ → Prop) (h : ∀ t < N * m, Q (t / m) (t % m)) :
    ∀ a < N, ∀ o < m, Q a o := by
  intro a ha o ho
  have hm : 0 < m := by omega
  have ht : a * m + o < N * m := by
    calc a * m + o < a * m + m := by omega
      _ = (a + 1) * m := by ring
      _ ≤ N * m := Nat.mul_le_mul_right m ha
  have h1 : (a * m + o) / m = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt ho, Nat.zero_add]
  have h2 : (a * m + o) % m = o := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]
  have := h (a * m + o) ht
  rwa [h1, h2] at this

/-- All outputs of a row from per-output checks. -/
theorem rowCheck_of_outputs (W L oA m : ℕ) (Rtab : List (List ℕ)) (Frow Grow : List ℕ)
    (hR : Rtab.length = m) (hG : Grow.length = m)
    (h : ∀ o < m, natAxpySp W L oA (Rtab.getD o []) Frow (Grow.getD o 0) = true) :
    rowCheck W L oA Rtab Frow Grow = true := by
  unfold rowCheck
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨o, ho, hpo⟩ := List.getElem_of_mem hp
  have ho' : o < m := by simpa [hR, hG] using ho
  rw [← hpo, List.getElem_zip]
  have h' := h o ho'
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at h'
  exact h'

/-- Axis-2 or axis-1 stage hypotheses of `x2ChainB` from flat per-output checks. -/
theorem x2b_rows_of_flat (W L oA N m : ℕ) (Rtab F G : List (List ℕ)) (hR : Rtab.length = m)
    (hG : ∀ a < N, (G.getD a []).length = m)
    (h : ∀ t < N * m, natAxpySp W L oA (Rtab.getD (t % m) []) (F.getD (t / m) [])
      (x2Tab G (t / m) (t % m)) = true) :
    ∀ a < N, rowCheck W L oA Rtab (F.getD a []) (G.getD a []) = true := by
  have h' := x2b_unflat N m (fun a o => natAxpySp W L oA (Rtab.getD o []) (F.getD a [])
    (x2Tab G a o) = true) h
  intro a ha
  exact rowCheck_of_outputs W L oA m Rtab _ _ hR (hG a ha) (fun o ho => h' a ha o ho)

/-- Regrouping hypothesis of `x2ChainB` from flat checks. -/
theorem x2b_regroup_of_flat (W n B N J : ℕ) (G H : List (List ℕ))
    (h : ∀ t < N * J, regroupOK W n B G H (t / J) (t % J) = true) :
    ∀ K' < N, ∀ b < J, x2Tab H K' b = regroupFiber W n B G K' b := by
  have h' := x2b_unflat N J (fun a o => regroupOK W n B G H a o = true) h
  intro K' hK' b hb
  exact regroupOK_eq W n B G H K' b (h' K' hK' b hb)

/-- Axis-0 stage hypothesis of `x2ChainB` (pairs selected by `pOK`) from flat checks. -/
theorem x2b_slots_of_flat (W n m B K J : ℕ) (Cs : List ℕ) (O T3 : List (List ℕ)) (tj tk : List ℕ)
    (h : ∀ t < K * J, (!(pOK tj tk (t % J) (t / J)) ||
      slotCheck W n m Cs (runOf W n ((t / J % B) * n) (x2Tab O (t / J / B) (t % J)))
        (x2Tab T3 (t / J) (t % J))) = true) :
    ∀ k < K, ∀ j < J, pOK tj tk j k = true →
      slotCheck W n m Cs (runOf W n ((k % B) * n) (x2Tab O (k / B) j)) (x2Tab T3 k j) = true := by
  have h' := x2b_unflat K J (fun k j => (!(pOK tj tk j k) ||
      slotCheck W n m Cs (runOf W n ((k % B) * n) (x2Tab O (k / B) j)) (x2Tab T3 k j)) = true) h
  intro k hk j hj hP
  have h1 := h' k hk j hj
  rw [hP] at h1
  simpa using h1

/-- Slot bounds of a table of super-fibers from flat checks. -/
theorem x2b_bounds_of_flat (W b L N C : ℕ) (F : List (List ℕ)) (hW : b + 2 ≤ W)
    (h : ∀ t < N * C, slotBoundCheck W b L (x2Tab F (t / C) (t % C)) = true) :
    ∀ a < N, ∀ c < C, x2Tab F a c < 2 ^ (W * L) ∧
      ∀ s < L, |ent W (W - 1) (x2Tab F a c) s| ≤ 2 ^ b := by
  have h' := x2b_unflat N C (fun a c => slotBoundCheck W b L (x2Tab F a c) = true) h
  intro a ha c hc
  exact slotBoundCheck_sound W b L _ hW (h' a ha c hc)

/-- Row `i` of a table against slot `i` of each packed column (one zip pass, one shift per entry). -/
noncomputable def colsRowOK (W oA : ℕ) (cs row : List ℕ) (i : ℕ) : Bool :=
  (List.zip cs row).all (fun p =>
    Nat.beq (((p.1 >>> (W * i)) &&& (2 ^ W - 1)) + 2 ^ oA) (p.2 + 2 ^ (W - 1)))

/-- Packed columns of a table from row-wise checks. -/
theorem cols_of_rows (W oA n m : ℕ) (cs : List ℕ) (R : List (List ℕ)) (hcs : cs.length = n)
    (hR : ∀ i < m, (R.getD i []).length = n)
    (h : ∀ i < m, colsRowOK W oA cs (R.getD i []) i = true) :
    ∀ a < n, ∀ i < m, ent W (W - 1) (cs.getD a 0) i = ((R.getD i []).getD a 0 : ℤ) - 2 ^ oA := by
  intro a ha i hi
  have ha' : a < cs.length := by omega
  have hb' : a < (R.getD i []).length := by rw [hR i hi]; exact ha
  have hz : a < (List.zip cs (R.getD i [])).length := by
    rw [List.length_zip, hcs, hR i hi, Nat.min_self]
    exact ha
  have h1 := h i hi
  unfold colsRowOK at h1
  have h2 := List.all_eq_true.mp h1 (cs[a], (R.getD i [])[a]) (by
    have := List.getElem_mem hz
    rwa [List.getElem_zip] at this)
  have h3 : ((cs[a] >>> (W * i)) &&& (2 ^ W - 1)) + 2 ^ oA = (R.getD i [])[a] + 2 ^ (W - 1) :=
    Nat.eq_of_beq_eq_true h2
  have hd : dig W cs[a] i = ((cs[a] >>> (W * i)) &&& (2 ^ W - 1)) := by
    unfold dig
    rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  have h4 : (((cs[a] >>> (W * i)) &&& (2 ^ W - 1) : ℕ) : ℤ) + 2 ^ oA =
      (((R.getD i [])[a] : ℕ) : ℤ) + 2 ^ (W - 1) := by exact_mod_cast h3
  rw [List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb']
  unfold ent
  rw [hd]
  linarith

end X2
end ThreeCopyQutritWerner
