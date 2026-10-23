module

public import ThreeCopyQutritWerner.FirstSiteBlocks

@[expose] public section


/-!
# Actual first-site ray contractions

Each contraction is a rectangular left/right multiplication of the original
matrix, so its rank is inherited. Binary-coordinate formulas retain the
complex conjugation on the contracted output ray.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {a d : Type*} [Fintype a] [Fintype d] [DecidableEq d]

/-- Tensoring with the actual first-site ray. -/
def firstSiteRayInjection (x : a → ℂ) : Matrix (a × d) d ℂ :=
  fun p r => if p.2 = r then x p.1 else 0

/-- Contract the original output against x and the original input against y. -/
def firstSiteContraction (C : Matrix (a × d) (a × d) ℂ) (x y : a → ℂ) :
    Matrix d d ℂ :=
  (firstSiteRayInjection x)ᴴ * C * firstSiteRayInjection y

/-- Both matrix multiplications can only decrease the original rank. -/
theorem firstSiteContraction_rank_le
    (C : Matrix (a × d) (a × d) ℂ) (x y : a → ℂ) :
    (firstSiteContraction C x y).rank ≤ C.rank := by
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Literal coefficients, with the output conjugation explicitly retained. -/
theorem firstSiteContraction_apply
    (C : Matrix (a × d) (a × d) ℂ) (x y : a → ℂ) (r s : d) :
    firstSiteContraction C x y r s =
      ∑ j, ∑ i, conj (x i) * C (i, r) (j, s) * y j := by
  simp [firstSiteContraction, firstSiteRayInjection, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Finset.sum_mul,
    apply_ite, ite_mul, mul_ite]

/-- Binary rays inside the actual three-dimensional first register. -/
theorem firstSiteContraction_binary_coordinates
    (C : Matrix (Fin 3 × d) (Fin 3 × d) ℂ) (z w : ℂ) :
    firstSiteContraction C ![1, z, 0] ![1, w, 0] =
      firstSiteBlock C 0 0 + w • firstSiteBlock C 0 1 +
        conj z • firstSiteBlock C 1 0 + (conj z * w) • firstSiteBlock C 1 1 := by
  ext r s
  simp only [firstSiteContraction_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_one, map_zero, zero_mul, mul_zero,
    one_mul, mul_one, zero_add, add_zero, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, firstSiteBlock, Matrix.submatrix_apply]
  ring

end ThreeCopyQutritWerner
