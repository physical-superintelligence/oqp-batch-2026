module

public import ThreeCopyQutritWerner.IdentityTensorRank
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section


/-!
# Finite rank-drop exceptions for an actual affine matrix pencil

A single member of rank at least two has a nonzero ordinary two-by-two
minor. Its literal determinant polynomial bounds all parameters where
the original matrix rank drops below two. No generic-rank assumption is
introduced without an actual anchor.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A nonzero ordinary two-by-two minor forces rank at least two. -/
theorem matrix_two_le_rank_of_entry_minor_ne_zero
    (A : Matrix m n ℂ) (i j : m) (k l : n)
    (h : A i k * A j l - A i l * A j k ≠ 0) : 2 ≤ A.rank := by
  have hd : (A.submatrix ![i, j] ![k, l]).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simpa only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  have hr := Matrix.rank_of_det_ne_zero hd
  have hl := Matrix.rank_submatrix_le A ![i, j] ![k, l]
  simp only [Fintype.card_fin] at hr
  omega

/-- Every rank-at-least-two matrix supplies actual indices of a nonzero
minor, with no distinctness or nonemptiness premise left to the caller. -/
theorem matrix_exists_entry_minor_ne_zero_of_two_le_rank
    (A : Matrix m n ℂ) (h : 2 ≤ A.rank) :
    ∃ i j k l, A i k * A j l - A i l * A j k ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hr := matrix_rank_le_one_of_two_minors_zero A
    (fun i j k l => sub_eq_zero.mp (hn i j k l))
  omega

/-- A single actual anchor controls the whole rank-drop exceptional set. -/
theorem affinePencil_rank_drop_finite
    (A B : Matrix m n ℂ) (z₀ : ℂ) (h : 2 ≤ (A + z₀ • B).rank) :
    {z : ℂ | (A + z • B).rank < 2}.Finite := by
  obtain ⟨i, j, k, l, hm⟩ :=
    matrix_exists_entry_minor_ne_zero_of_two_le_rank (A + z₀ • B) h
  let p : Polynomial ℂ :=
    (Polynomial.C (A i k) + Polynomial.X * Polynomial.C (B i k)) *
      (Polynomial.C (A j l) + Polynomial.X * Polynomial.C (B j l)) -
    (Polynomial.C (A i l) + Polynomial.X * Polynomial.C (B i l)) *
      (Polynomial.C (A j k) + Polynomial.X * Polynomial.C (B j k))
  have he (z : ℂ) : p.eval z =
      (A + z • B) i k * (A + z • B) j l -
        (A + z • B) i l * (A + z • B) j k := by
    simp only [p, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
  have hp : p ≠ 0 := by
    intro hp
    apply hm
    rw [← he z₀, hp, Polynomial.eval_zero]
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  intro z hz
  change p.eval z = 0
  rw [he z]
  by_contra hminor
  have hr := matrix_two_le_rank_of_entry_minor_ne_zero (A + z • B) i j k l hminor
  exact (not_lt_of_ge hr) hz

/-- If the actual affine family has rank at most two everywhere, one
rank-two anchor makes it exactly rank two outside a finite set. -/
theorem affinePencil_rank_two_off_finite
    (A B : Matrix m n ℂ) (hr : ∀ z : ℂ, (A + z • B).rank ≤ 2)
    (z₀ : ℂ) (h : (A + z₀ • B).rank = 2) :
    ∃ s : Set ℂ, s.Finite ∧ ∀ z ∉ s, (A + z • B).rank = 2 := by
  refine ⟨{z : ℂ | (A + z • B).rank < 2},
    affinePencil_rank_drop_finite A B z₀ h.ge, ?_⟩
  intro z hz
  have hz' : ¬ (A + z • B).rank < 2 := hz
  exact le_antisymm (hr z) (Nat.le_of_not_gt hz')

end ThreeCopyQutritWerner
