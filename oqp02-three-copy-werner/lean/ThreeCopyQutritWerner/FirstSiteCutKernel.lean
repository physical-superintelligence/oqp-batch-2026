module

public import ThreeCopyQutritWerner.FirstSiteContraction
public import ThreeCopyQutritWerner.TwoCutQuadratic
public import ThreeCopyQutritWerner.TwoCutMain

@[expose] public section


/-!
# Additivity of cut-zero contractions of one actual rank-two matrix

The cut form need not be positive on arbitrary matrices. Each sum and
difference used here is an actual contraction of the same original matrix,
so the proved rank-two cut inequality applies to both terms.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq b] [DecidableEq c]

theorem cutForm_add_eq_zero_of_rank_controls
    (A B : Matrix (b × c) (b × c) ℂ)
    (hA : cutForm A = 0) (hB : cutForm B = 0)
    (hp : (A + B).rank ≤ 2) (hm : (A - B).rank ≤ 2) :
    cutForm (A + B) = 0 := by
  have hpn := cutForm_nonneg_of_rank_le_two (A + B) hp
  have hmn := cutForm_nonneg_of_rank_le_two (A - B) hm
  have he := cutForm_parallelogram A B
  rw [hA, hB] at he
  linarith

theorem firstSiteContraction_add_left
    (C : Matrix (a × b × c) (a × b × c) ℂ) (x y z : a → ℂ) :
    firstSiteContraction C (x + y) z =
      firstSiteContraction C x z + firstSiteContraction C y z := by
  ext r s
  simp only [firstSiteContraction_apply, Pi.add_apply, map_add, add_mul,
    Finset.sum_add_distrib, Matrix.add_apply]

theorem firstSiteContraction_sub_left
    (C : Matrix (a × b × c) (a × b × c) ℂ) (x y z : a → ℂ) :
    firstSiteContraction C (x - y) z =
      firstSiteContraction C x z - firstSiteContraction C y z := by
  ext r s
  simp only [firstSiteContraction_apply, Pi.sub_apply, map_sub, sub_mul,
    Finset.sum_sub_distrib, Matrix.sub_apply]

theorem firstSiteContraction_add_right
    (C : Matrix (a × b × c) (a × b × c) ℂ) (x y z : a → ℂ) :
    firstSiteContraction C x (y + z) =
      firstSiteContraction C x y + firstSiteContraction C x z := by
  ext r s
  simp only [firstSiteContraction_apply, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, Matrix.add_apply]

theorem firstSiteContraction_sub_right
    (C : Matrix (a × b × c) (a × b × c) ℂ) (x y z : a → ℂ) :
    firstSiteContraction C x (y - z) =
      firstSiteContraction C x y - firstSiteContraction C x z := by
  ext r s
  simp only [firstSiteContraction_apply, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib, Matrix.sub_apply]

theorem firstSiteContraction_cutForm_add_left
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2)
    (x y z : a → ℂ)
    (hx : cutForm (firstSiteContraction C x z) = 0)
    (hy : cutForm (firstSiteContraction C y z) = 0) :
    cutForm (firstSiteContraction C (x + y) z) = 0 := by
  have hp := (firstSiteContraction_rank_le C (x + y) z).trans hC
  have hm := (firstSiteContraction_rank_le C (x - y) z).trans hC
  rw [firstSiteContraction_add_left] at hp ⊢
  rw [firstSiteContraction_sub_left] at hm
  exact cutForm_add_eq_zero_of_rank_controls _ _ hx hy hp hm

theorem firstSiteContraction_cutForm_add_right
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2)
    (x y z : a → ℂ)
    (hy : cutForm (firstSiteContraction C x y) = 0)
    (hz : cutForm (firstSiteContraction C x z) = 0) :
    cutForm (firstSiteContraction C x (y + z)) = 0 := by
  have hp := (firstSiteContraction_rank_le C x (y + z)).trans hC
  have hm := (firstSiteContraction_rank_le C x (y - z)).trans hC
  rw [firstSiteContraction_add_right] at hp ⊢
  rw [firstSiteContraction_sub_right] at hm
  exact cutForm_add_eq_zero_of_rank_controls _ _ hy hz hp hm

end ThreeCopyQutritWerner
