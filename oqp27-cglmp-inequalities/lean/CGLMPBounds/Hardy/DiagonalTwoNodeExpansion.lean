module

public import CGLMPBounds.Hardy.MatrixIndexCyclePower

@[expose] public section


/-! Literal two-node diagonal resolvent and ordered-cycle rational expansion.
All powers arise from the actual matrix product; the positive count retains
repeated indices and has no cyclic-quotient normalization. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagonal_inverse_of_ne_zero (d : ι → ℂ) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.diagonal_apply, Matrix.one_apply, hd i]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, h]

theorem resolvent_diagonal_of_ne (d : ι → ℂ) {z : ℂ} (hz : ∀ i, z ≠ d i) :
    resolvent (Matrix.diagonal d) z = Matrix.diagonal (fun i => (z - d i)⁻¹) := by
  have hshift : algebraMap ℂ (Matrix ι ι ℂ) z - Matrix.diagonal d =
      Matrix.diagonal (fun i => z - d i) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Pi.algebraMap_def]
    · simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Pi.algebraMap_def, h]
  rw [resolvent, ← Matrix.nonsing_inv_eq_ringInverse, hshift]
  exact diagonal_inverse_of_ne_zero _ (fun i => sub_ne_zero.mpr (hz i))

lemma cyclePositiveCount_le (σ : ι → Bool) {n : ℕ} (v : Fin n → ι) :
    cyclePositiveCount σ v ≤ n := by
  simpa only [cyclePositiveCount, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun k => σ (v k) = true))

lemma cycle_product_two_values (σ : ι → Bool) {n : ℕ} (v : Fin n → ι) (A B : ℂ) :
    (∏ k, if σ (v k) then A else B) =
      A ^ cyclePositiveCount σ v * B ^ (n - cyclePositiveCount σ v) := by
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun k => σ (v k) = true)
  have hc : (Finset.univ.filter (fun k : Fin n => ¬σ (v k) = true)).card =
      n - cyclePositiveCount σ v := by
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    unfold cyclePositiveCount
    omega
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, hc, cyclePositiveCount]

theorem diagonal_two_node_weighted_resolvent_trace
    (σ : ι → Bool) (Y : Matrix ι ι ℂ) (m : ℕ) (a b : ℂ)
    {z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) :
    z ^ m * Matrix.trace ((resolvent
      (Matrix.diagonal (fun i => if σ i then a else b)) z * Y) ^ (m + 2)) =
    ∑ v : Fin (m + 2) → ι,
      (z ^ m / ((z - a) ^ cyclePositiveCount σ v *
        (z - b) ^ (m + 2 - cyclePositiveCount σ v))) *
          matrixIndexCycleWeight Y (m + 1) v := by
  rw [resolvent_diagonal_of_ne _ (fun i => by cases h : σ i <;> simp [h, hza, hzb]),
    diagonal_mul_trace_pow_eq_sum_index_cycles, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hp : (∏ k, (z - (if σ (v k) then a else b))⁻¹) =
      (z - a)⁻¹ ^ cyclePositiveCount σ v *
        (z - b)⁻¹ ^ (m + 2 - cyclePositiveCount σ v) := by
    convert cycle_product_two_values σ v (z - a)⁻¹ (z - b)⁻¹ using 1
    apply Finset.prod_congr rfl
    intro k _
    cases h : σ (v k) <;> simp [h]
  rw [hp]
  simp only [inv_pow, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

end
end CGLMPBounds.Hardy
