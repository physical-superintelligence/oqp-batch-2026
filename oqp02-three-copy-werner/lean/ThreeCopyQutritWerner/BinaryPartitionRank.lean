module

public import ThreeCopyQutritWerner.BinaryPartitionCoordinates

@[expose] public section


/-!
# Rank of a tensor with an actual rank-one factor

The full matrix factors through the other matrix, and a nonzero entry of
the rank-one factor recovers that other matrix as a scalar submatrix. This
retains the original tensor entries, without a spectral or support premise.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem binaryPartition_rank_one_kronecker_rank_le
    (p q : a → ℂ) (T : Matrix b b ℂ) :
    ((fun i j => p i * q j) ⊗ₖ T).rank ≤ T.rank := by
  let A : Matrix (a × b) b ℂ := fun i k => if i.2 = k then p i.1 else 0
  let B : Matrix b (a × b) ℂ := fun k j => if k = j.2 then q j.1 else 0
  have he : (fun i j => p i * q j) ⊗ₖ T = A * T * B := by
    ext i j
    change (p i.1 * q j.1) * T i.2 j.2 =
      ∑ k : b, (∑ l : b, (if i.2 = l then p i.1 else 0) * T l k) *
        (if k = j.2 then q j.1 else 0)
    simp [ite_mul, mul_ite, mul_assoc, mul_comm, mul_left_comm]
  rw [he]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem binaryPartition_rank_one_kronecker_rank
    (p q : a → ℂ) (hp : p ≠ 0) (hq : q ≠ 0) (T : Matrix b b ℂ) :
    ((fun i j => p i * q j) ⊗ₖ T).rank = T.rank := by
  apply le_antisymm (binaryPartition_rank_one_kronecker_rank_le p q T)
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hp (funext hn)
  obtain ⟨j, hj⟩ : ∃ j, q j ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hq (funext hn)
  have he : (((fun i j => p i * q j) ⊗ₖ T).submatrix
      (fun k => (i, k)) (fun k => (j, k))) = (p i * q j) • T := by
    ext k l
    rfl
  have hr := Matrix.rank_submatrix_le ((fun i j => p i * q j) ⊗ₖ T)
    (fun k => (i, k)) (fun k => (j, k))
  rw [he, Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero hi hj))] at hr
  exact hr

/-- The ordinary skew two-ray matrix always factors through its two actual
vectors; degeneracies do not need to be excluded for the rank upper bound. -/
theorem binaryPartition_skew_two_ray_rank_le_two (r s : b → ℂ) :
    Matrix.rank (fun i j : b => r i * s j - s i * r j) ≤ 2 := by
  apply (rank_le_iff_exists_mul _ 2).mpr
  refine ⟨(fun i k => ![r i, s i] k), (fun k j => ![s j, -r j] k), ?_⟩
  ext i j
  change r i * s j - s i * r j =
    ∑ k : Fin 2, ![r i, s i] k * ![s j, -r j] k
  simp [Fin.sum_univ_two, sub_eq_add_neg]

end ThreeCopyQutritWerner
