module

public import CGLMPBounds.Circulation.Hodge

@[expose] public section


/-!
# Every edge belongs to d - 2 triangles

The weighted identity is used in (D.15) and in the proof of D.1. It is proved
for arbitrary symmetric real edge weights, without positivity assumptions.
-/

namespace CGLMPBounds.Circulation

open Finset

theorem sorted_triangle_edge_count {ι : Type*} [Fintype ι] [LinearOrder ι]
    (p : ι → ι → ℝ) (hp : ∀ i j, p i j = p j i) (hp0 : ∀ i, p i i = 0) :
    (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then p i j + p j k + p i k else 0) =
      ((Fintype.card ι : ℝ) - 2) * ∑ i, ∑ j, if i < j then p i j else 0 := by
  classical
  let f : ι → ι → ι → ℝ := fun i j k =>
    if i ≠ j ∧ j ≠ k ∧ i ≠ k then p i j + p j k + p i k else 0
  have hs12 (i j k : ι) : f i j k = f j i k := by
    by_cases hij : i = j
    · subst j; simp [f]
    by_cases hjk : j = k
    · subst k; simp [f]
    by_cases hik : i = k
    · subst k; simp [f]
    have hijk : i ≠ j ∧ j ≠ k ∧ i ≠ k := ⟨hij, hjk, hik⟩
    have hjik : j ≠ i ∧ i ≠ k ∧ j ≠ k := ⟨Ne.symm hij, hik, hjk⟩
    simp only [f, if_pos hijk, if_pos hjik]
    rw [hp j i]
    ring
  have hs23 (i j k : ι) : f i j k = f i k j := by
    by_cases hij : i = j
    · subst j; simp [f]
    by_cases hjk : j = k
    · subst k; simp [f]
    by_cases hik : i = k
    · subst k; simp [f]
    have hijk : i ≠ j ∧ j ≠ k ∧ i ≠ k := ⟨hij, hjk, hik⟩
    have hikj : i ≠ k ∧ k ≠ j ∧ i ≠ j := ⟨hik, Ne.symm hjk, hij⟩
    simp only [f, if_pos hijk, if_pos hikj]
    rw [hp k j]
    ring
  have hf0 (i k : ι) : f i i k = 0 := by simp [f]
  have hT := sum_triple_symmetric f hs12 hs23 hf0
  have hE := sum_pair_symmetric p hp hp0
  have hexpand (i j k : ι) : f i j k =
      p i j + p j k + p i k - (if i = j then 2 * p i k else 0) -
        (if j = k then 2 * p i j else 0) - (if i = k then 2 * p i j else 0) := by
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k; simp [f, hp0]
      · simp [f, hp0, hik]; ring
    by_cases hjk : j = k
    · subst k; simp [f, hp0, hij]; ring
    by_cases hik : i = k
    · subst k; simp [f, hp0, hij, Ne.symm hij, hp j i]; ring
    · simp [f, hij, hjk, hik]
  have hmain : (∑ i, ∑ j, ∑ k, (p i j + p j k + p i k)) =
      3 * Fintype.card ι * ∑ i, ∑ j, p i j := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hdiag1 : (∑ i, ∑ j, ∑ k, if i = j then 2 * p i k else 0) =
      2 * ∑ i, ∑ j, p i j := by
    calc
      _ = ∑ i, ∑ k, ∑ j, if i = j then 2 * p i k else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := by simp [Finset.mul_sum]
  have hdiag2 : (∑ i, ∑ j, ∑ k, if j = k then 2 * p i j else 0) =
      2 * ∑ i, ∑ j, p i j := by
    simp [Finset.mul_sum]
  have hdiag3 : (∑ i, ∑ j, ∑ k, if i = k then 2 * p i j else 0) =
      2 * ∑ i, ∑ j, p i j := by
    simp [Finset.mul_sum]
  have hordered : (∑ i, ∑ j, ∑ k, f i j k) =
      3 * ((Fintype.card ι : ℝ) - 2) * ∑ i, ∑ j, p i j := by
    simp_rw [hexpand, Finset.sum_sub_distrib]
    rw [hmain, hdiag1, hdiag2, hdiag3]
    ring
  have hsorted : (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0) =
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then p i j + p j k + p i k else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with h
    · simp [f, h.1.ne, h.2.ne, (lt_trans h.1 h.2).ne]
    · rfl
  rw [hT, hE, hsorted] at hordered
  nlinarith

/-- Only increasing edges occur in the conclusion, so their weights need not
be supplied as a symmetric array. -/
theorem sorted_triangle_edge_count_oriented {ι : Type*} [Fintype ι] [LinearOrder ι]
    (q : ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then q i j + q j k + q i k else 0) =
      ((Fintype.card ι : ℝ) - 2) * ∑ i, ∑ j, if i < j then q i j else 0 := by
  classical
  let p : ι → ι → ℝ := fun i j => if i < j then q i j else if j < i then q j i else 0
  have hp (i j : ι) : p i j = p j i := by
    rcases lt_trichotomy i j with h | h | h
    · simp [p, h, not_lt_of_gt h]
    · subst j; rfl
    · simp [p, h, not_lt_of_gt h]
  have hp0 (i : ι) : p i i = 0 := by simp [p]
  have h := sorted_triangle_edge_count p hp hp0
  have he : (∑ i, ∑ j, if i < j then p i j else 0) =
      ∑ i, ∑ j, if i < j then q i j else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij <;> simp [p, hij]
  have ht : (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then p i j + p j k + p i k else 0) =
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then q i j + q j k + q i k else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with hij
    · simp [p, hij.1, hij.2, lt_trans hij.1 hij.2]
    · rfl
  simpa only [he, ht] using h

end CGLMPBounds.Circulation
