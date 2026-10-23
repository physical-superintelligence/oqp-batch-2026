module

public import CGLMPBounds.Defs.PinchingCycles

@[expose] public section


/-! Actual finite entry expansion of matrix powers. No trace or resolvent
identity is assumed; ordered cycles arise by closing ordinary matrix paths. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_fin_succ_tuple (n : ℕ) (f : (Fin (n + 1) → ι) → ℂ) :
    (∑ v, f v) = ∑ i : ι, ∑ v : Fin n → ι, f (Fin.cons i v) := by
  symm
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => ι))
    (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)

theorem matrix_pow_entry_eq_sum_index_paths (Y : Matrix ι ι ℂ) (n : ℕ) (i j : ι) :
    (Y ^ (n + 1)) i j = ∑ v : Fin n → ι, matrixIndexPathWeight Y i j n v := by
  induction n generalizing i with
  | zero => simp [matrixIndexPathWeight]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply, sum_fin_succ_tuple]
    apply Finset.sum_congr rfl
    intro k _
    rw [ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [matrixIndexPathWeight, Fin.cons_zero, Fin.cons_succ]

theorem matrix_trace_pow_eq_sum_index_cycles (Y : Matrix ι ι ℂ) (n : ℕ) :
    Matrix.trace (Y ^ (n + 1)) =
      ∑ v : Fin (n + 1) → ι, matrixIndexCycleWeight Y n v := by
  rw [Matrix.trace, sum_fin_succ_tuple]
  apply Finset.sum_congr rfl
  intro i _
  change (Y ^ (n + 1)) i i = _
  rw [matrix_pow_entry_eq_sum_index_paths]
  apply Finset.sum_congr rfl
  intro v _
  simp only [matrixIndexCycleWeight, Fin.cons_zero, Fin.cons_succ]

lemma matrixIndexPathWeight_diagonal_mul (d : ι → ℂ) (Y : Matrix ι ι ℂ)
    (i j : ι) (n : ℕ) (v : Fin n → ι) :
    matrixIndexPathWeight (Matrix.diagonal d * Y) i j n v =
      (d i * ∏ k, d (v k)) * matrixIndexPathWeight Y i j n v := by
  induction n generalizing i with
  | zero => simp [matrixIndexPathWeight, Matrix.diagonal_mul]
  | succ n ih =>
    simp only [matrixIndexPathWeight, Matrix.diagonal_mul, ih, Fin.prod_univ_succ]
    ring

theorem matrixIndexCycleWeight_diagonal_mul (d : ι → ℂ) (Y : Matrix ι ι ℂ)
    (n : ℕ) (v : Fin (n + 1) → ι) :
    matrixIndexCycleWeight (Matrix.diagonal d * Y) n v =
      (∏ k, d (v k)) * matrixIndexCycleWeight Y n v := by
  unfold matrixIndexCycleWeight
  rw [matrixIndexPathWeight_diagonal_mul, Fin.prod_univ_succ]

theorem diagonal_mul_trace_pow_eq_sum_index_cycles (d : ι → ℂ)
    (Y : Matrix ι ι ℂ) (n : ℕ) :
    Matrix.trace ((Matrix.diagonal d * Y) ^ (n + 1)) =
      ∑ v : Fin (n + 1) → ι,
        (∏ k, d (v k)) * matrixIndexCycleWeight Y n v := by
  rw [matrix_trace_pow_eq_sum_index_cycles]
  exact Finset.sum_congr rfl (fun v _ => matrixIndexCycleWeight_diagonal_mul d Y n v)

end
end CGLMPBounds.Hardy
