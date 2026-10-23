module

public import ThreeCopyQutritWerner.BinaryZeros

@[expose] public section


/-!
# The symmetric feature `H(C, p)` (manuscript eq. (23) and Appendix C)

Write `C = X B` with `X = [x, y]` (Section 4.1). The source bivector
`p = (x ⊗ y - y ⊗ x)/√2`, regarded as a skew matrix, is `P = X ε Xᵀ/√2` (`bivecMat`,
`bivecMat_apply`), and `H(C, p) = (C P - P Cᵀ)/2` (`hFeature`). This file proves the
certificate-free part of eq. (23) and the algebraic formula of Appendix C:

* `Pᵀ = -P` and `Hᵀ = H` (`bivecMat_transpose`, `hFeature_transpose_of_skew`);
* `H = X (B X - (Tr C)/2 · I₂) ε Xᵀ/√2` (`hFeature_formula`, Appendix C); hence
  `H = X N` for some `N`, i.e. `ran H ⊆ ran X`, and `rank H ≤ 2` (`hFeature_eq_mul`,
  `rank_hFeature_le`); when `X` spans `ran C` this is the manuscript's `ran H ⊆ ran C`;
* if `B X = κ I₂` then `H = 0` (`hFeature_eq_zero_of_compress`); if `X` has a left inverse and
  `B` a right inverse (as for a rank-two `C = X B`), then `C² = κ C` forces `B X = κ I₂`, so
  `H = 0` (`compress_eq_smul_of_sq`, `hFeature_eq_zero_of_sq`).
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

variable {n : Type*} [Fintype n]

/-- `H(C, P) = (C P - P Cᵀ)/2` (manuscript eq. (23)). -/
def hFeature (C P : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 / 2 : ℂ) • (C * P - P * Cᵀ)

/-- Entrywise, `bivecMat X i j = (x_i y_j - y_i x_j)/√2`. -/
theorem bivecMat_apply (X : Matrix n (Fin 2) ℂ) (i j : n) :
    bivecMat X i j = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (X i 0 * X j 1 - X i 1 * X j 0) := by
  rw [bivecMat, Matrix.smul_apply, smul_eq_mul]
  congr 1
  simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, epsMat] <;> ring

theorem bivecMat_transpose (X : Matrix n (Fin 2) ℂ) : (bivecMat X)ᵀ = -bivecMat X := by
  rw [bivecMat, Matrix.transpose_smul, transpose_mul_eps_mul_transpose, smul_neg]

/-- `H` is symmetric whenever `P` is skew. -/
theorem hFeature_transpose_of_skew (C P : Matrix n n ℂ) (hP : Pᵀ = -P) :
    (hFeature C P)ᵀ = hFeature C P := by
  unfold hFeature
  rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    hP, Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, sub_neg_eq_add,
    neg_add_eq_sub]

theorem hFeature_transpose (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) :
    (hFeature (X * B) (bivecMat X))ᵀ = hFeature (X * B) (bivecMat X) :=
  hFeature_transpose_of_skew _ _ (bivecMat_transpose X)

/-- The `2 × 2` identity `M ε - ε Mᵀ = 2 (M - (Tr M)/2 · I) ε`. -/
theorem mul_eps_sub_eps_mul_transpose (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * epsMat - epsMat * Mᵀ = (2 : ℂ) • ((M - (M.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      epsMat) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [epsMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.one_apply,
      Matrix.vecMul, dotProduct] <;> ring

theorem hFeature_bivecMat (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) :
    hFeature (X * B) (bivecMat X) = ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) / 2) •
      (X * (B * X * epsMat - epsMat * (B * X)ᵀ) * Xᵀ) := by
  unfold hFeature bivecMat
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, smul_smul, Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · ring
  · rw [Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

/-- Appendix C: `H = X (B X - (Tr C)/2 · I₂) ε Xᵀ/√2` for `C = X B`. -/
theorem hFeature_formula (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) :
    hFeature (X * B) (bivecMat X) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (X * ((B * X - ((X * B).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * epsMat) * Xᵀ) := by
  rw [hFeature_bivecMat, mul_eps_sub_eps_mul_transpose, Matrix.trace_mul_comm X B,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1 <;> first | rfl | ring

/-- `ran H ⊆ ran X`: `H = X N`. -/
theorem hFeature_eq_mul (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) :
    hFeature (X * B) (bivecMat X) = X * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      ((B * X - ((X * B).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * epsMat * Xᵀ)) := by
  rw [hFeature_formula, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

/-- `rank H ≤ 2` (manuscript eq. (23)). -/
theorem rank_hFeature_le (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) :
    (hFeature (X * B) (bivecMat X)).rank ≤ 2 :=
  rank_le_two_of_eq_mul _ _ _ (hFeature_eq_mul X B)

/-- Appendix C: if the compression `B X` is a multiple of the identity, then `H = 0`. -/
theorem hFeature_eq_zero_of_compress (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) (κ : ℂ)
    (h : B * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    hFeature (X * B) (bivecMat X) = 0 := by
  have hz : κ • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      ((κ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.trace, Fin.sum_univ_two, Matrix.one_apply] <;>
      ring
  rw [hFeature_formula, Matrix.trace_mul_comm X B, h, hz, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.zero_mul, smul_zero]

/-- If `X` has a left inverse and `B` a right inverse (as for a rank-two `C = X B` with `X` having
two columns), then `C² = κ C` forces `B X = κ I₂`. -/
theorem compress_eq_smul_of_sq (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ)
    (L : Matrix (Fin 2) n ℂ) (R : Matrix n (Fin 2) ℂ) (hL : L * X = 1) (hR : B * R = 1) (κ : ℂ)
    (h : X * B * (X * B) = κ • (X * B)) :
    B * X = κ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 : B * X = L * (X * B * (X * B)) * R := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc L X, hL, Matrix.one_mul, hR, Matrix.mul_one]
  rw [h1, h, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc L X, hL, Matrix.one_mul, hR]

/-- Appendix C: `C² = κ C` implies `H = 0`, for `C = X B` with `X` left invertible and `B`
right invertible. -/
theorem hFeature_eq_zero_of_sq (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ)
    (L : Matrix (Fin 2) n ℂ) (R : Matrix n (Fin 2) ℂ) (hL : L * X = 1) (hR : B * R = 1) (κ : ℂ)
    (h : X * B * (X * B) = κ • (X * B)) :
    hFeature (X * B) (bivecMat X) = 0 :=
  hFeature_eq_zero_of_compress X B κ (compress_eq_smul_of_sq X B L R hL hR κ h)

end ThreeCopyQutritWerner

end
