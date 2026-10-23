module

public import ThreeCopyQutritWerner.PPTRegion

@[expose] public section


/-!
# Exact local comparison for the product-ray analytic branch

For the canonical local product ray e₀, L is the cross-term contraction in the
rank-two energy and D⁻¹=diag(2,1,1) is its local Schur weight. The comparison
B is the physical partial transpose of L†D⁻¹L. Explicit rational Gram matrices
prove A−B≥0 and A+3B≥0, replacing the quoted generalized eigenvalues 1 and −1/3
with exact positive identities. The three-site Schur identity and its equality
consequences are proved in later modules.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder Kronecker

namespace ThreeCopyQutritWerner

set_option maxHeartbeats 2000000

abbrev ProductRayPair := Fin 3 × Fin 3

/-- The positive swap comparison used for a rank-one summand. -/
def productRayA : Matrix ProductRayPair ProductRayPair ℂ :=
  1 - (1 / 2 : ℂ) • swapOp (Fin 3)

/-- Cross-term contraction for a source containing the canonical ray e₀. -/
def productRayL : Matrix (Fin 3) ProductRayPair ℂ := fun k ij =>
  (if ij.1 = 0 ∧ ij.2 = k then 1 else 0) -
    (1 / 2 : ℂ) * (if k = 0 ∧ ij.1 = ij.2 then 1 else 0)

/-- Inverse of the local positive quadratic coefficient for the e₀ summand. -/
def productRayDinv : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![2, 1, 1]

/-- Physical partial transpose is taken only after the Schur contraction. -/
def productRayB : Matrix ProductRayPair ProductRayPair ℂ :=
  partialTranspose (productRayLᴴ * productRayDinv * productRayL)

def productRayQRows : Matrix (Fin 3) ProductRayPair ℂ := ![
  fun ij => if ij = (1, 0) then 1 else 0,
  fun ij => if ij = (2, 0) then 1 else 0,
  fun ij => (if ij = (1, 2) then 1 else 0) - (if ij = (2, 1) then 1 else 0)]

def productRayDiagonalRows : Matrix (Fin 3) ProductRayPair ℂ :=
  fun k ij => if ij = (k, k) then 1 else 0

def productRayPRows : Matrix (Fin 3) ProductRayPair ℂ := ![
  fun ij => 2 * (if ij = (0, 1) then 1 else 0) - (if ij = (1, 0) then 1 else 0),
  fun ij => 2 * (if ij = (0, 2) then 1 else 0) - (if ij = (2, 0) then 1 else 0),
  fun ij => (if ij = (1, 2) then 1 else 0) + (if ij = (2, 1) then 1 else 0)]

def productRayAntiRows : Matrix (Fin 3) ProductRayPair ℂ := ![
  fun ij => (if ij = (0, 1) then 1 else 0) - (if ij = (1, 0) then 1 else 0),
  fun ij => (if ij = (0, 2) then 1 else 0) - (if ij = (2, 0) then 1 else 0),
  fun ij => (if ij = (1, 2) then 1 else 0) - (if ij = (2, 1) then 1 else 0)]

/-- Exact upper generalized comparison, with a three-row rational Gram factor. -/
theorem productRayA_sub_B_eq_gram :
    productRayA - productRayB = productRayQRowsᴴ * productRayQRows := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [productRayA, productRayB, productRayL, productRayDinv, productRayQRows,
      partialTranspose, swapOp, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, Fin.sum_univ_succ, map_ofNat]

/-- Exact lower generalized comparison; every term is an explicit positive Gram term. -/
theorem productRayA_add_three_B_eq_gram :
    productRayA + (3 : ℂ) • productRayB =
      (2 : ℝ) • (productRayDiagonalRowsᴴ * productRayDiagonalRows) +
        productRayPRowsᴴ * productRayPRows := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [productRayA, productRayB, productRayL, productRayDinv,
      productRayDiagonalRows, productRayPRows, partialTranspose, swapOp,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Fin.sum_univ_succ, map_ofNat]

/-- A is uniformly bounded below by half the identity. -/
theorem productRayA_sub_half_eq_gram :
    productRayA - (1 / 2 : ℂ) • (1 : Matrix ProductRayPair ProductRayPair ℂ) =
      (1 / 2 : ℝ) • (productRayAntiRowsᴴ * productRayAntiRows) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [productRayA, productRayAntiRows, swapOp, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, map_ofNat]

theorem productRayA_sub_B_posSemidef : (productRayA - productRayB).PosSemidef := by
  rw [productRayA_sub_B_eq_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem productRayA_add_three_B_posSemidef :
    (productRayA + (3 : ℂ) • productRayB).PosSemidef := by
  rw [productRayA_add_three_B_eq_gram]
  exact ((Matrix.posSemidef_conjTranspose_mul_self _).smul (by norm_num : (0 : ℝ) ≤ 2)).add
    (Matrix.posSemidef_conjTranspose_mul_self _)

theorem productRayA_sub_half_posSemidef :
    (productRayA - (1 / 2 : ℂ) • (1 : Matrix ProductRayPair ProductRayPair ℂ)).PosSemidef := by
  rw [productRayA_sub_half_eq_gram]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- The Gram factor vanishes exactly when its three defect coordinates vanish. -/
theorem productRayQ_mulVec_eq_zero_iff (w : ProductRayPair → ℂ) :
    productRayQRows *ᵥ w = 0 ↔ w (1, 0) = 0 ∧ w (2, 0) = 0 ∧ w (1, 2) = w (2, 1) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [productRayQRows, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_succ] at h0 h1 h2
    exact ⟨h0, h1, by simpa only [← sub_eq_add_neg, sub_eq_zero] using h2⟩
  · rintro ⟨h10, h20, h12⟩
    ext i
    fin_cases i <;>
      simp [productRayQRows, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
        Fin.sum_univ_succ, h10, h20, h12]

end ThreeCopyQutritWerner
