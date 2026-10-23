module

public import CGLMPBounds.Hardy.PinchingIndexCycles

@[expose] public section


/-! Arbitrary polynomial weight and perturbation order in the two-node
matrix resolvent expansion. The pinched subtraction is literally the sum
of mixed ordered index cycles, with no spectral or combinatorial oracle. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem diagonal_two_node_weighted_resolvent_trace_general
    (σ : ι → Bool) (Y : Matrix ι ι ℂ) (n M : ℕ) (a b : ℂ)
    {z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) :
    z ^ M * Matrix.trace ((resolvent
      (Matrix.diagonal (fun i => if σ i then a else b)) z * Y) ^ (n + 1)) =
    ∑ v : Fin (n + 1) → ι,
      (z ^ M / ((z - a) ^ cyclePositiveCount σ v *
        (z - b) ^ (n + 1 - cyclePositiveCount σ v))) * matrixIndexCycleWeight Y n v := by
  rw [resolvent_diagonal_of_ne _ (fun i => by cases h : σ i <;> simp [h, hza, hzb]),
    diagonal_mul_trace_pow_eq_sum_index_cycles, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hp : (∏ k, (z - (if σ (v k) then a else b))⁻¹) =
      (z - a)⁻¹ ^ cyclePositiveCount σ v *
        (z - b)⁻¹ ^ (n + 1 - cyclePositiveCount σ v) := by
    convert cycle_product_two_values σ v (z - a)⁻¹ (z - b)⁻¹ using 1
    apply Finset.prod_congr rfl
    intro k _
    cases h : σ (v k) <;> simp [h]
  rw [hp]
  simp only [inv_pow, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem diagonal_two_node_mixed_resolvent_trace
    (σ : ι → Bool) (Y : Matrix ι ι ℂ) (n M : ℕ) (a b : ℂ)
    {z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) :
    let H := Matrix.diagonal (fun i => if σ i then a else b)
    z ^ M * (Matrix.trace ((resolvent H z * Y) ^ (n + 1)) -
      Matrix.trace ((resolvent H z * positivePinchingPart (involutionFromSigns σ) Y) ^ (n + 1))) =
    ∑ v : Fin (n + 1) → ι,
      if 1 ≤ cyclePositiveCount σ v ∧ cyclePositiveCount σ v < n + 1 then
        (z ^ M / ((z - a) ^ cyclePositiveCount σ v *
          (z - b) ^ (n + 1 - cyclePositiveCount σ v))) * matrixIndexCycleWeight Y n v
      else 0 := by
  dsimp only
  rw [mul_sub, diagonal_two_node_weighted_resolvent_trace_general σ Y n M a b hza hzb,
    diagonal_two_node_weighted_resolvent_trace_general σ
      (positivePinchingPart (involutionFromSigns σ) Y) n M a b hza hzb,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [matrixIndexCycleWeight_pinching]
  by_cases hm : 1 ≤ cyclePositiveCount σ v ∧ cyclePositiveCount σ v < n + 1
  · simp [hm, show cyclePositiveCount σ v ≤ n by omega]
  · have hn : ¬(1 ≤ cyclePositiveCount σ v ∧ cyclePositiveCount σ v ≤ n) := by omega
    simp [hm, hn]

end
end CGLMPBounds.Hardy
