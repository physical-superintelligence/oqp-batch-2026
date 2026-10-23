module

public import CGLMPBounds.Hardy.DiagonalTwoNodeExpansion

@[expose] public section


/-! Actual pinching removes precisely the mixed ordered index cycles.
The path proof keeps every edge and repeated index, so no informal cyclic
quotient or matrix commutativity is used in the C.10 coefficient comparison. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma positivePinching_part_signs_apply (σ : ι → Bool) (Y : Matrix ι ι ℂ) (i j : ι) :
    positivePinchingPart (involutionFromSigns σ) Y i j =
      if σ i = σ j then Y i j else 0 := by
  simp only [positivePinchingPart, involutionFromSigns, Matrix.smul_apply, Matrix.add_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, smul_eq_mul]
  cases hi : σ i <;> cases hj : σ j <;> simp [hi, hj] <;> ring

lemma matrixIndexPathWeight_pinching (σ : ι → Bool) (Y : Matrix ι ι ℂ)
    (i j : ι) (n : ℕ) (v : Fin n → ι) :
    matrixIndexPathWeight (positivePinchingPart (involutionFromSigns σ) Y) i j n v =
      if σ i = σ j ∧ ∀ k, σ (v k) = σ i then matrixIndexPathWeight Y i j n v else 0 := by
  induction n generalizing i j with
  | zero => simp [matrixIndexPathWeight, positivePinching_part_signs_apply]
  | succ n ih =>
    simp only [matrixIndexPathWeight, positivePinching_part_signs_apply, ih,
      Fin.forall_fin_succ]
    cases hi : σ i <;> cases hj : σ j <;> cases hv : σ (v 0) <;>
      simp [hi, hj, hv]

lemma matrixIndexCycleWeight_pinching_uniform (σ : ι → Bool) (Y : Matrix ι ι ℂ)
    (n : ℕ) (v : Fin (n + 1) → ι) :
    matrixIndexCycleWeight (positivePinchingPart (involutionFromSigns σ) Y) n v =
      if ∀ k, σ (v k) = σ (v 0) then matrixIndexCycleWeight Y n v else 0 := by
  unfold matrixIndexCycleWeight
  rw [matrixIndexPathWeight_pinching]
  simp only [Fin.forall_fin_succ, and_self, eq_self_iff_true, true_and]

lemma cyclePositiveCount_eq_zero_iff (σ : ι → Bool) {n : ℕ} (v : Fin n → ι) :
    cyclePositiveCount σ v = 0 ↔ ∀ k, σ (v k) = false := by
  unfold cyclePositiveCount
  simpa using (Finset.card_filter_eq_zero_iff
    (s := (Finset.univ : Finset (Fin n))) (p := fun k => σ (v k) = true))

lemma cyclePositiveCount_eq_length_iff (σ : ι → Bool) {n : ℕ} (v : Fin n → ι) :
    cyclePositiveCount σ v = n ↔ ∀ k, σ (v k) = true := by
  unfold cyclePositiveCount
  simpa using (Finset.card_filter_eq_iff
    (s := (Finset.univ : Finset (Fin n))) (p := fun k => σ (v k) = true))

lemma index_cycle_uniform_iff_unmixed (σ : ι → Bool) (n : ℕ) (v : Fin (n + 1) → ι) :
    (∀ k, σ (v k) = σ (v 0)) ↔
      cyclePositiveCount σ v = 0 ∨ cyclePositiveCount σ v = n + 1 := by
  constructor
  · intro hall
    cases h0 : σ (v 0) with
    | false => exact Or.inl ((cyclePositiveCount_eq_zero_iff σ v).mpr (fun k => by rw [hall k, h0]))
    | true => exact Or.inr ((cyclePositiveCount_eq_length_iff σ v).mpr (fun k => by rw [hall k, h0]))
  · intro h
    rcases h with h | h
    · have hall := (cyclePositiveCount_eq_zero_iff σ v).mp h
      intro k
      rw [hall k, hall 0]
    · have hall := (cyclePositiveCount_eq_length_iff σ v).mp h
      intro k
      rw [hall k, hall 0]

theorem matrixIndexCycleWeight_pinching (σ : ι → Bool) (Y : Matrix ι ι ℂ)
    (n : ℕ) (v : Fin (n + 1) → ι) :
    matrixIndexCycleWeight (positivePinchingPart (involutionFromSigns σ) Y) n v =
      if 1 ≤ cyclePositiveCount σ v ∧ cyclePositiveCount σ v < n + 1 then 0
      else matrixIndexCycleWeight Y n v := by
  rw [matrixIndexCycleWeight_pinching_uniform]
  simp only [index_cycle_uniform_iff_unmixed]
  have hle := cyclePositiveCount_le σ v
  by_cases hm : 1 ≤ cyclePositiveCount σ v ∧ cyclePositiveCount σ v < n + 1
  · have hnot : ¬ (cyclePositiveCount σ v = 0 ∨ cyclePositiveCount σ v = n + 1) := by omega
    simp only [hm, hnot, if_pos, if_neg, ite_true, ite_false, and_self]
  · have hu : cyclePositiveCount σ v = 0 ∨ cyclePositiveCount σ v = n + 1 := by omega
    simp only [hm, hu, if_pos, if_neg, ite_true, ite_false, and_self]

end
end CGLMPBounds.Hardy
