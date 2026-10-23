module

public import ThreeCopyQutritWerner.TwoCutInputSplit
public import ThreeCopyQutritWerner.OrthogonalProjectionRange

@[expose] public section


/-!
# Literal input columns and their original block ranges

Coordinate injections realize every physical block as actual multiplication.
When a block retains the rank of the full input column, its adjoint has the
same original range as that column's adjoint. No common range is supplied.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

variable {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a] [DecidableEq d]

/-- Inclusion of the original second-register coordinates at a fixed first index. -/
def firstSiteCoordinateInjection (i : a) : Matrix (a × d) d ℂ :=
  fun p r => if p.1 = i then if p.2 = r then 1 else 0 else 0

/-- The literal original input column, before any projection normalization. -/
def firstSiteColumn (C : Matrix (a × d) (a × d) ℂ) (k : a) :
    Matrix (a × d) d ℂ := fun p r => C p (k, r)

theorem firstSiteColumn_eq_mul (C : Matrix (a × d) (a × d) ℂ) (k : a) :
    firstSiteColumn C k = C * firstSiteCoordinateInjection k := by
  ext p r
  simp [firstSiteColumn, firstSiteCoordinateInjection, Matrix.mul_apply,
    Fintype.sum_prod_type, mul_ite]

theorem firstSiteBlock_eq_injection_mul_column
    (C : Matrix (a × d) (a × d) ℂ) (i k : a) :
    firstSiteBlock C i k = (firstSiteCoordinateInjection i)ᴴ * firstSiteColumn C k := by
  ext r s
  simp [firstSiteBlock, firstSiteColumn, firstSiteCoordinateInjection,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, apply_ite, ite_mul]

theorem firstSiteColumn_rank_le (C : Matrix (a × d) (a × d) ℂ) (k : a) :
    (firstSiteColumn C k).rank ≤ C.rank := by
  rw [firstSiteColumn_eq_mul]
  exact Matrix.rank_mul_le_left _ _

theorem firstSiteBlock_rank_le_column (C : Matrix (a × d) (a × d) ℂ) (i k : a) :
    (firstSiteBlock C i k).rank ≤ (firstSiteColumn C k).rank := by
  rw [firstSiteBlock_eq_injection_mul_column]
  exact Matrix.rank_mul_le_right _ _

/-- A full-rank original block determines the whole input column's adjoint range. -/
theorem firstSiteBlock_adjoint_range_eq_column
    (C : Matrix (a × d) (a × d) ℂ) (i k : a)
    (hr : (firstSiteBlock C i k).rank = (firstSiteColumn C k).rank) :
    LinearMap.range ((firstSiteBlock C i k)ᴴ).mulVecLin =
      LinearMap.range ((firstSiteColumn C k)ᴴ).mulVecLin := by
  rw [firstSiteBlock_eq_injection_mul_column, Matrix.conjTranspose_mul]
  apply matrix_range_mul_eq_of_rank_eq
  rw [← Matrix.conjTranspose_mul, Matrix.rank_conjTranspose, Matrix.rank_conjTranspose]
  simpa only [← firstSiteBlock_eq_injection_mul_column] using hr

end ThreeCopyQutritWerner
