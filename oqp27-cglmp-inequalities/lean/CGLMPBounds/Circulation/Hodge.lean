module

public import Mathlib

@[expose] public section


/-!
# The finite complete-graph Hodge identity behind (D.13)

This module develops ordered and sorted identities for arbitrary real skew edge arrays with
zero divergence, then specializes to translation-invariant cyclic coefficients as in (D.13).
-/

namespace CGLMPBounds.Circulation

open Finset

theorem sum_triple_rotate {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ j, ∑ k, ∑ i, f i j k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

/-- The ordered triangle pairing is `3d` times the ordered edge pairing when the first
skew array has zero divergence. No positivity, matrix model or spectral hypothesis is needed. -/
theorem ordered_hodge_identity {ι : Type*} [Fintype ι]
    (t b : ι → ι → ℝ) (ht : ∀ i j, t i j = -t j i)
    (hrow : ∀ i, ∑ j, t i j = 0) :
    (∑ i, ∑ j, ∑ k,
      (t i j + t j k + t k i) * (b i j + b j k + b k i)) =
      3 * Fintype.card ι * ∑ i, ∑ j, t i j * b i j := by
  classical
  have hcol (j : ι) : ∑ i, t i j = 0 := by
    calc
      (∑ i, t i j) = ∑ i, -t j i := Finset.sum_congr rfl (fun i _ => ht i j)
      _ = 0 := by rw [Finset.sum_neg_distrib, hrow, neg_zero]
  have hcycle (i j : ι) : ∑ k, (t i j + t j k + t k i) = Fintype.card ι * t i j := by
    simp only [Finset.sum_add_distrib, hrow, hcol, add_zero, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have h1 : (∑ i, ∑ j, ∑ k, (t i j + t j k + t k i) * b i j) =
      Fintype.card ι * ∑ i, ∑ j, t i j * b i j := by
    simp_rw [← Finset.sum_mul, hcycle]
    simp only [Finset.mul_sum, mul_assoc]
  have h2 : (∑ i, ∑ j, ∑ k, (t i j + t j k + t k i) * b j k) =
      Fintype.card ι * ∑ i, ∑ j, t i j * b i j := by
    calc
      _ = ∑ j, ∑ k, ∑ i, (t j k + t k i + t i j) * b j k := by
        rw [sum_triple_rotate]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := h1
  have h3 : (∑ i, ∑ j, ∑ k, (t i j + t j k + t k i) * b k i) =
      Fintype.card ι * ∑ i, ∑ j, t i j * b i j := by
    calc
      _ = ∑ k, ∑ i, ∑ j, (t k i + t i j + t j k) * b k i := by
        rw [sum_triple_rotate, sum_triple_rotate]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := h1
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [h1, h2, h3]
  ring

/-- A symmetric edge sum with zero diagonal counts every increasing edge twice. -/
theorem sum_pair_symmetric {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * ∑ i, ∑ j, if i < j then f i j else 0 := by
  classical
  let g : ι → ι → ℝ := fun i j => if i < j then f i j else 0
  have hp (i j : ι) : f i j = g i j + g j i := by
    rcases lt_trichotomy i j with h | h | h
    · simp [g, h, not_lt_of_gt h]
    · subst j; simp [g, hd]
    · simp [g, h, not_lt_of_gt h, hs i j]
  have hswap : (∑ i, ∑ j, g j i) = ∑ i, ∑ j, g i j := Finset.sum_comm
  calc
    _ = ∑ i, ∑ j, (g i j + g j i) := by simp_rw [← hp]
    _ = 2 * ∑ i, ∑ j, g i j := by
      simp_rw [Finset.sum_add_distrib]
      rw [hswap]
      ring
    _ = _ := rfl

/-- A symmetric triangle sum vanishing on repeated vertices counts every increasing
triangle six times. No positivity assumption is used. -/
theorem sum_triple_symmetric {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ι → ℝ)
    (hs12 : ∀ i j k, f i j k = f j i k)
    (hs23 : ∀ i j k, f i j k = f i k j)
    (hd : ∀ i k, f i i k = 0) :
    (∑ i, ∑ j, ∑ k, f i j k) =
      6 * ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0 := by
  classical
  let g : ι → ι → ι → ℝ := fun i j k => if i < j ∧ j < k then f i j k else 0
  have hd13 (i j : ι) : f i j i = 0 := by rw [hs23, hd]
  have hd23 (i j : ι) : f i j j = 0 := by rw [hs12, hd13]
  have hc (i j k : ι) : f i j k = f j k i := by rw [hs12 i j k, hs23 j i k]
  have hr (i j k : ι) : f i j k = f k j i := by
    rw [hs12 i j k, hs23 j i k, hs12 j k i]
  have hp (i j k : ι) : f i j k =
      g i j k + g i k j + g j i k + g j k i + g k i j + g k j i := by
    rcases lt_trichotomy i j with hij | hij | hji
    · rcases lt_trichotomy j k with hjk | hjk | hkj
      · have hik := lt_trans hij hjk
        simp [g, hij, hjk, hik, not_lt_of_gt hij, not_lt_of_gt hjk, not_lt_of_gt hik]
      · subst k
        simp [g, hij, not_lt_of_gt hij, hd23]
      · rcases lt_trichotomy i k with hik | hik | hki
        · simp [g, hij, hik, hkj, not_lt_of_gt hij, not_lt_of_gt hik,
            not_lt_of_gt hkj, hs23 i j k]
        · subst k
          simp [g, hij, not_lt_of_gt hij, hd13]
        · simp [g, hij, hki, hkj, not_lt_of_gt hij, not_lt_of_gt hki,
            not_lt_of_gt hkj, ← hc k i j]
    · subst j
      simp [g, hd, hd13, hd23]
    · rcases lt_trichotomy i k with hik | hik | hki
      · have hjk := lt_trans hji hik
        simp [g, hji, hik, hjk, not_lt_of_gt hji, not_lt_of_gt hik,
          not_lt_of_gt hjk, hs12 i j k]
      · subst k
        simp [g, hji, not_lt_of_gt hji, hd13]
      · rcases lt_trichotomy j k with hjk | hjk | hkj
        · simp [g, hji, hjk, hki, not_lt_of_gt hji, not_lt_of_gt hjk,
            not_lt_of_gt hki, hc i j k]
        · subst k
          simp [g, hji, not_lt_of_gt hji, hd23]
        · simp [g, hji, hkj, hki, not_lt_of_gt hji, not_lt_of_gt hkj,
            not_lt_of_gt hki, hr i j k]
  have h12 : (∑ i, ∑ j, ∑ k, g j i k) = ∑ i, ∑ j, ∑ k, g i j k :=
    Finset.sum_comm
  have h23 : (∑ i, ∑ j, ∑ k, g i k j) = ∑ i, ∑ j, ∑ k, g i j k := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  have hc1 : (∑ i, ∑ j, ∑ k, g j k i) = ∑ i, ∑ j, ∑ k, g i j k :=
    sum_triple_rotate _
  have hc2 : (∑ i, ∑ j, ∑ k, g k i j) = ∑ i, ∑ j, ∑ k, g i j k :=
    (sum_triple_rotate _).symm
  have hr1 : (∑ i, ∑ j, ∑ k, g k j i) = ∑ i, ∑ j, ∑ k, g i j k := by
    calc
      _ = ∑ i, ∑ k, ∑ j, g k j i := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := hc1
  calc
    _ = ∑ i, ∑ j, ∑ k,
        (g i j k + g i k j + g j i k + g j k i + g k i j + g k j i) := by
      simp_rw [← hp]
    _ = 6 * ∑ i, ∑ j, ∑ k, g i j k := by
      simp_rw [Finset.sum_add_distrib]
      rw [h23, h12, hc1, hc2, hr1]
      ring
    _ = _ := rfl

/-- Sorted-index form of the complete-graph Hodge identity. This is the finite-sum
algebra in (D.13); the manuscript's cyclic coefficient array still needs specialization. -/
theorem sorted_hodge_identity {ι : Type*} [Fintype ι] [LinearOrder ι]
    (t b : ι → ι → ℝ) (ht : ∀ i j, t i j = -t j i)
    (hb : ∀ i j, b i j = -b j i) (hrow : ∀ i, ∑ j, t i j = 0) :
    (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
      (t i j + t j k - t i k) * (b i j + b j k - b i k) else 0) =
      Fintype.card ι * ∑ i, ∑ j, if i < j then t i j * b i j else 0 := by
  classical
  let f : ι → ι → ι → ℝ := fun i j k =>
    (t i j + t j k + t k i) * (b i j + b j k + b k i)
  have ht0 (i : ι) : t i i = 0 := by have := ht i i; linarith
  have hb0 (i : ι) : b i i = 0 := by have := hb i i; linarith
  have hs12 (i j k : ι) : f i j k = f j i k := by
    dsimp [f]
    rw [ht j i, ht i k, ht k j, hb j i, hb i k, hb k j]
    ring
  have hs23 (i j k : ι) : f i j k = f i k j := by
    dsimp [f]
    rw [ht j i, ht i k, ht k j, hb j i, hb i k, hb k j]
    ring
  have hd (i k : ι) : f i i k = 0 := by
    simp [f, ht0, hb0, ht k i, hb k i]
  have hT := sum_triple_symmetric f hs12 hs23 hd
  have hE := sum_pair_symmetric (fun i j => t i j * b i j)
    (fun i j => by rw [ht i j, hb i j]; ring)
    (fun i => by rw [ht0 i, zero_mul])
  have hH := ordered_hodge_identity t b ht hrow
  change (∑ i, ∑ j, ∑ k, f i j k) = _ at hH
  rw [hT, hE] at hH
  have hsorted : (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0) =
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        (t i j + t j k - t i k) * (b i j + b j k - b i k) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    split_ifs
    · dsimp [f]
      rw [ht k i, hb k i]
      ring
    · rfl
  rw [hsorted] at hH
  nlinarith

/-- The antisymmetric cyclic coefficient `t_h=e_{-h}-e_h`. -/
def cyclicSkew {ι : Type*} [AddGroup ι] (e : ι → ℝ) (i j : ι) : ℝ :=
  e (i - j) - e (j - i)

theorem cyclicSkew_skew {ι : Type*} [AddGroup ι] (e : ι → ℝ) (i j : ι) :
    cyclicSkew e i j = -cyclicSkew e j i := by unfold cyclicSkew; ring

/-- Translation invariance makes the cyclic skew array divergence-free. -/
theorem cyclicSkew_row {ι : Type*} [Fintype ι] [AddCommGroup ι]
    (e : ι → ℝ) (i : ι) : ∑ j, cyclicSkew e i j = 0 := by
  simp only [cyclicSkew, Finset.sum_sub_distrib]
  have hl : (∑ j, e (i - j)) = ∑ j, e j := (Equiv.subLeft i).sum_comp e
  have hr : (∑ j, e (j - i)) = ∑ j, e j := (Equiv.subRight i).sum_comp e
  rw [hl, hr, sub_self]

/-- The identity (D.13) for cyclic coefficients and arbitrary complex edge values with
skew imaginary part. Ordering is used only to count each edge and triangle once. -/
theorem cyclic_form_decomposition {ι : Type*} [Fintype ι] [LinearOrder ι] [AddCommGroup ι]
    [Nonempty ι] (e : ι → ℝ) (z : ι → ι → ℂ)
    (hz : ∀ i j, (z i j).im = -(z j i).im) :
    (∑ i, ∑ j, if i < j then
        e (j - i) * (1 - (z i j).re) + e (i - j) * (z i j).im else 0) =
      2 * (∑ i, ∑ j, if i < j then
        e (j - i) * ((1 - (z i j).re + (z i j).im) / 2) else 0) +
      (1 / Fintype.card ι : ℝ) *
        ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
          (cyclicSkew e i j + cyclicSkew e j k - cyclicSkew e i k) *
            ((z i j).im + (z j k).im - (z i k).im) else 0 := by
  classical
  have hH := sorted_hodge_identity (cyclicSkew e) (fun i j => (z i j).im)
    (cyclicSkew_skew e) hz (cyclicSkew_row e)
  rw [hH]
  have hd : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, one_div_mul_cancel hd, one_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [cyclicSkew] <;> ring

end CGLMPBounds.Circulation
