module

public import ThreeCopyQutritWerner.CoherentReserveAlgebra
public import ThreeCopyQutritWerner.ZeroReserveSign
public import Mathlib.Tactic.Abel

@[expose] public section


/-!
# The actual positive coherent pencil and its four-phase reserve

The columns are the same two logical columns at every phase. Positivity and
rank at most two are proved from the literal matrix product, and the reserve
average is an exact four-term identity in the original physical coordinates.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

/-- The literal coherent positive source, without a normalization or rank surrogate. -/
def coherentPositiveSource {n k : Type*} [Fintype k]
    (X Y : Matrix n k ℂ) (z : ℂ) : Matrix n n ℂ :=
  (X + z • Y) * (X + z • Y)ᴴ

/-- Every member of the coherent pencil is positive semidefinite. -/
theorem coherentPositiveSource_posSemidef {n k : Type*} [Fintype n] [Fintype k]
    (X Y : Matrix n k ℂ) (z : ℂ) : (coherentPositiveSource X Y z).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

/-- Its actual rank is bounded by its shared logical column dimension. -/
theorem coherentPositiveSource_rank_le {n k : Type*} [Fintype n] [Fintype k]
    (X Y : Matrix n k ℂ) (z : ℂ) :
    (coherentPositiveSource X Y z).rank ≤ Fintype.card k :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- Exact constant, radial and first-harmonic terms of the actual source. -/
theorem coherentPositiveSource_expansion {n k : Type*} [Fintype k]
    (X Y : Matrix n k ℂ) (z : ℂ) :
    coherentPositiveSource X Y z = X * Xᴴ + (Complex.normSq z : ℂ) • (Y * Yᴴ) +
      (conj z • (X * Yᴴ) + z • (X * Yᴴ)ᴴ) := by
  simp only [coherentPositiveSource, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Complex.star_def, Complex.mul_conj, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← Complex.mul_conj]
  ring

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- No positivity premise is supplied: every two-column coherent source has
nonnegative actual reserve whenever the physical space has at least two coordinates. -/
theorem coherentPositiveSource_reserve_nonneg [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (X Y : Matrix (a × b × c) (Fin 2) ℂ) (z : ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) :
    0 ≤ zeroReserve (coherentPositiveSource X Y z) := by
  exact zeroReserve_posSemidef_rank_le_two _ (coherentPositiveSource_posSemidef X Y z)
    (by simpa using coherentPositiveSource_rank_le X Y z) hn

/-- Exact average over all four unit phases, retaining the same X and Y. -/
theorem coherentPositiveSource_four_phase {k : Type*} [Fintype k]
    (X Y : Matrix (a × b × c) k ℂ) :
    zeroReserve (coherentPositiveSource X Y 1) +
      zeroReserve (coherentPositiveSource X Y (-1)) +
      zeroReserve (coherentPositiveSource X Y Complex.I) +
      zeroReserve (coherentPositiveSource X Y (-Complex.I)) =
        4 * zeroReserve (X * Xᴴ + Y * Yᴴ) + 8 * zeroReserve (X * Yᴴ) := by
  let A := X * Xᴴ + Y * Yᴴ
  let C := X * Yᴴ
  have h1 : coherentPositiveSource X Y 1 = A + (C + Cᴴ) := by
    simp [coherentPositiveSource_expansion, A, C]
  have h2 : coherentPositiveSource X Y (-1) = A - (C + Cᴴ) := by
    rw [coherentPositiveSource_expansion]
    simp only [map_neg, map_one, Complex.normSq_neg, Complex.normSq_one,
      Complex.ofReal_one, one_smul, neg_smul, sub_eq_add_neg, neg_add_rev, A, C]
    abel
  have h3 : coherentPositiveSource X Y Complex.I = A - Complex.I • (C - Cᴴ) := by
    rw [coherentPositiveSource_expansion]
    simp only [Complex.conj_I, Complex.normSq_I, Complex.ofReal_one, one_smul,
      neg_smul, smul_sub, sub_eq_add_neg, neg_add_rev, neg_neg, A, C]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  have h4 : coherentPositiveSource X Y (-Complex.I) = A + Complex.I • (C - Cᴴ) := by
    rw [coherentPositiveSource_expansion]
    simp only [map_neg, Complex.conj_I, Complex.normSq_neg, Complex.normSq_I,
      Complex.ofReal_one, one_smul, neg_smul, smul_sub, sub_eq_add_neg, neg_neg, A, C]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  rw [h1, h2, h3, h4]
  have h := zeroReserve_four_phase A C
  dsimp [A, C] at h ⊢
  linarith

/-- The four-term positivity inequality for the literal two-column pencil. -/
theorem coherentPositiveSource_reserve_pair_bound
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) :
    -zeroReserve (X * Xᴴ + Y * Yᴴ) / 2 ≤ zeroReserve (X * Yᴴ) := by
  have h := coherentPositiveSource_four_phase X Y
  have h1 := coherentPositiveSource_reserve_nonneg X Y 1 hn
  have h2 := coherentPositiveSource_reserve_nonneg X Y (-1) hn
  have h3 := coherentPositiveSource_reserve_nonneg X Y Complex.I hn
  have h4 := coherentPositiveSource_reserve_nonneg X Y (-Complex.I) hn
  linarith

end ThreeCopyQutritWerner
