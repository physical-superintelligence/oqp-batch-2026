module

public import CGLMPBounds.Circulation.TriangleCount

@[expose] public section


/-!
# Finite weighted assembly of the D.1 scalar margin

This lemma isolates the finite summation step. Its hypotheses are subsequently
to be supplied by the scalar integral estimates and the fourth-root circulation
bound. It is not a substitute statement for D.1.
-/

namespace CGLMPBounds.Circulation

open Finset

theorem finite_triangle_coercivity {ι : Type*} [Fintype ι] [LinearOrder ι]
    (hd : 3 ≤ Fintype.card ι) (p a : ι → ι → ℝ) (ω C : ι → ι → ι → ℝ) (c : ℝ)
    (hp : ∀ i j, i < j → 0 ≤ p i j)
    (hC : ∀ i j k, i < j → j < k → |C i j k| ≤ 5 * (p i j + p j k + p i k))
    (ha : ∀ i j k, i < j → j < k →
      5 * ((Fintype.card ι : ℝ) - 2) * |ω i j k| ≤
        2 * Fintype.card ι * (a i j - c) ∧
      5 * ((Fintype.card ι : ℝ) - 2) * |ω i j k| ≤
        2 * Fintype.card ι * (a j k - c) ∧
      5 * ((Fintype.card ι : ℝ) - 2) * |ω i j k| ≤
        2 * Fintype.card ι * (a i k - c)) :
    2 * c * (∑ i, ∑ j, if i < j then p i j else 0) ≤
      2 * (∑ i, ∑ j, if i < j then a i j * p i j else 0) +
      (1 / (Fintype.card ι : ℝ)) *
        ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then ω i j k * C i j k else 0 := by
  classical
  let N : ℝ := Fintype.card ι
  have hN3 : 3 ≤ N := by
    dsimp [N]
    exact_mod_cast hd
  have hN0 : 0 < N := by linarith
  have hN2 : 0 < N - 2 := by linarith
  let q : ι → ι → ℝ := fun i j => (a i j - c) * p i j
  have hlocal (i j k : ι) (hij : i < j) (hjk : j < k) :
      -(2 * N) * (q i j + q j k + q i k) ≤
        (N - 2) * (ω i j k * C i j k) := by
    have hc := hC i j k hij hjk
    have hw := mul_le_mul_of_nonneg_left hc (abs_nonneg (ω i j k))
    have hbase : -(5 * |ω i j k| * (p i j + p j k + p i k)) ≤
        ω i j k * C i j k := by
      have hab := neg_abs_le (ω i j k * C i j k)
      rw [abs_mul] at hab
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hbase hN2.le
    have hmargin := ha i j k hij hjk
    have h1 := mul_le_mul_of_nonneg_right hmargin.1 (hp i j hij)
    have h2 := mul_le_mul_of_nonneg_right hmargin.2.1 (hp j k hjk)
    have h3 := mul_le_mul_of_nonneg_right hmargin.2.2 (hp i k (lt_trans hij hjk))
    dsimp [q, N] at *
    nlinarith
  have hsum : (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        -(2 * N) * (q i j + q j k + q i k) else 0) ≤
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        (N - 2) * (ω i j k * C i j k) else 0 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    split_ifs with h
    · exact hlocal i j k h.1 h.2
    · rfl
  have hL : (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        -(2 * N) * (q i j + q j k + q i k) else 0) =
      -(2 * N) * ((N - 2) * ∑ i, ∑ j, if i < j then q i j else 0) := by
    rw [← sorted_triangle_edge_count_oriented q]
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  have hR : (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        (N - 2) * (ω i j k * C i j k) else 0) =
      (N - 2) * ∑ i, ∑ j, ∑ k,
        if i < j ∧ j < k then ω i j k * C i j k else 0 := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [hL, hR] at hsum
  have hcancel : -(2 * N) * (∑ i, ∑ j, if i < j then q i j else 0) ≤
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then ω i j k * C i j k else 0 := by
    apply le_of_mul_le_mul_left (a0 := hN2)
    convert hsum using 1 <;> ring
  have hq : (∑ i, ∑ j, if i < j then q i j else 0) =
      (∑ i, ∑ j, if i < j then a i j * p i j else 0) -
        c * ∑ i, ∑ j, if i < j then p i j else 0 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp [q] <;> ring
  rw [hq] at hcancel
  have hout := mul_le_mul_of_nonneg_left hcancel (le_of_lt (one_div_pos.mpr hN0))
  have hsimp : (1 / N) * (-(2 * N) *
      ((∑ i, ∑ j, if i < j then a i j * p i j else 0) -
        c * ∑ i, ∑ j, if i < j then p i j else 0)) =
      -(2 * (∑ i, ∑ j, if i < j then a i j * p i j else 0)) +
        2 * c * ∑ i, ∑ j, if i < j then p i j else 0 := by
    field_simp [hN0.ne']
    <;> ring
  rw [hsimp] at hout
  change _ ≤ _ + (1 / N) * _
  linarith

end CGLMPBounds.Circulation
