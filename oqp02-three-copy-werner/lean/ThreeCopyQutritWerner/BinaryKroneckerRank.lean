module

public import ThreeCopyQutritWerner.BinaryZeros
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.LinearCombination

@[expose] public section


/-!
# Rank-two binary Kronecker sums

A direct cubic-minor argument for the binary-carrier algebra used in Appendix C.3.
No diagonalizability or Jordan normal-form assumption is made. This does not
supply the separate reduction of an arbitrary thin endpoint zero to this carrier.
-/

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Scalar plus the two traceless single-site parts, in original tensor order. -/
def binaryKroneckerSum (c : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  c • 1 + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A +
    B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Remove scalar and both single-site components of an actual binary matrix. -/
def binaryCorrelation (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  M - (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ptraceL M) -
    (1 / 2 : ℂ) • (ptraceR M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) +
    (M.trace / 4) • 1

/-- Rank at most two annihilates every cofactor of an actual four-dimensional matrix. -/
theorem adjugate_fin_four_eq_zero_of_rank_le_two (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hM : M.rank ≤ 2) : M.adjugate = 0 := by
  ext i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hd : (M.submatrix j.succAbove i.succAbove).det = 0 := by
    by_contra hn
    have hr := Matrix.rank_of_det_ne_zero hn
    have hl := (Matrix.rank_submatrix_le M j.succAbove i.succAbove).trans hM
    rw [hr] at hl
    norm_num at hl
  simp only [hd, mul_zero, Matrix.zero_apply]

/-- Exact adjugate polynomial, including nilpotent local matrices. -/
theorem binaryKroneckerSum_adjugate (c : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.trace = 0) (hB : B.trace = 0) :
    ((binaryKroneckerSum c A B).submatrix finProdFinEquiv.symm
      finProdFinEquiv.symm).adjugate =
    ((c * (c ^ 2 + A.det + B.det)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) +
      (-c ^ 2 - A.det + B.det) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A) +
      (-c ^ 2 + A.det - B.det) • (B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) +
      (2 * c) • (B ⊗ₖ A)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
  have ha : A 1 1 = -A 0 0 := by
    have ht : A 0 0 + A 1 1 = 0 := by
      simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] using hA
    linear_combination ht
  have hb : B 1 1 = -B 0 0 := by
    have ht : B 0 0 + B 1 1 = 0 := by
      simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] using hB
    linear_combination ht
  ext i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;> fin_cases j <;>
    norm_num [binaryKroneckerSum, Matrix.det_fin_three, Matrix.det_fin_two,
      Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.succAbove, ha, hb] <;> ring

/-- Correlation extraction keeps exactly the product of the two traceless local parts. -/
theorem binaryCorrelation_local_polynomial (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.trace = 0) (hB : B.trace = 0) (d e f g : ℂ) :
    binaryCorrelation (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) +
      e • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A) +
      f • (B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) + g • (B ⊗ₖ A)) =
      g • (B ⊗ₖ A) := by
  have ha : A 1 1 = -A 0 0 := by
    have ht : A 0 0 + A 1 1 = 0 := by
      simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] using hA
    linear_combination ht
  have hb : B 1 1 = -B 0 0 := by
    have ht : B 0 0 + B 1 1 = 0 := by
      simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] using hB
    linear_combination ht
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [binaryCorrelation, ptraceL, ptraceR, Matrix.trace, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply, ha, hb] <;> ring

/-- The nonzero-scalar rank-two branch forces one local traceless part to vanish.
This is valid for arbitrary complex local matrices, including defective ones. -/
theorem binaryKroneckerSum_local_zero_of_rank_le_two
    (c : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.trace = 0) (hB : B.trace = 0) (hc : c ≠ 0)
    (hr : (binaryKroneckerSum c A B).rank ≤ 2) : A = 0 ∨ B = 0 := by
  let P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    (c * (c ^ 2 + A.det + B.det)) • 1 +
      (-c ^ 2 - A.det + B.det) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A) +
      (-c ^ 2 + A.det - B.det) • (B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) +
      (2 * c) • (B ⊗ₖ A)
  have hp : P = 0 := by
    have hminor := adjugate_fin_four_eq_zero_of_rank_le_two
      ((binaryKroneckerSum c A B).submatrix
        (finProdFinEquiv (m := 2) (n := 2)).symm
        (finProdFinEquiv (m := 2) (n := 2)).symm)
      ((Matrix.rank_submatrix_le _ _ _).trans hr)
    rw [binaryKroneckerSum_adjugate c A B hA hB] at hminor
    ext i j
    have hij := congrFun (congrFun hminor (finProdFinEquiv i)) (finProdFinEquiv j)
    simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.zero_apply] using hij
  have hcorr := binaryCorrelation_local_polynomial A B hA hB
    (c * (c ^ 2 + A.det + B.det)) (-c ^ 2 - A.det + B.det)
    (-c ^ 2 + A.det - B.det) (2 * c)
  change binaryCorrelation P = (2 * c) • (B ⊗ₖ A) at hcorr
  rw [hp] at hcorr
  have hzero : (2 * c) • (B ⊗ₖ A) = 0 := by
    rw [← hcorr]
    ext i j
    simp [binaryCorrelation, ptraceL, ptraceR, Matrix.trace, Matrix.diag_apply,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.kroneckerMap_apply]
  have ht : B ⊗ₖ A = 0 := (smul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by norm_num) hc)
  by_cases hb : B = 0
  · exact Or.inr hb
  · left
    obtain ⟨i, j, hij⟩ : ∃ i j, B i j ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hb
      ext i j
      exact hn i j
    ext k l
    have h := congrFun (congrFun ht (i, k)) (j, l)
    simp only [Matrix.kroneckerMap_apply, Matrix.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_left hij

/-- The scalar-free binary carrier has the required skew spin transform. -/
theorem binaryKroneckerSum_zero_scalar_spin
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.trace = 0) (hB : B.trace = 0) :
    (binaryKroneckerSum 0 A B * epsJ₂)ᵀ = -(binaryKroneckerSum 0 A B * epsJ₂) := by
  have ha : A 1 1 = -A 0 0 := by
    have ht : A 0 0 + A 1 1 = 0 := by
      simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] using hA
    linear_combination ht
  have hb : B 1 1 = -B 0 0 := by
    have ht : B 0 0 + B 1 1 = 0 := by
      simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] using hB
    linear_combination ht
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [binaryKroneckerSum, epsJ₂, epsMat, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply, ha, hb] <;> ring

end ThreeCopyQutritWerner
