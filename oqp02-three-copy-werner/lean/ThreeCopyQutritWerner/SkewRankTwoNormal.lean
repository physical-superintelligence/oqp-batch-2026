module

public import ThreeCopyQutritWerner.BinaryZeros
public import ThreeCopyQutritWerner.RankTwo
public import Mathlib.Tactic.LinearCombination

@[expose] public section


/-!
# The actual orthonormal normal form of a rank-two complex skew matrix

Ordinary transpose, not conjugate transpose, is used in the skew condition.
The range factorization is derived from the actual rank. Compression therefore
gives a genuine two-dimensional skew matrix, and its coefficient has exactly
the Frobenius normalization used in the zero families.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Every actual two-dimensional skew matrix is a scalar multiple of epsilon. -/
theorem skew_fin_two_eq_smul_eps (S : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : Sᵀ = -S) : S = S 0 1 • epsMat := by
  have h00 := congrFun (congrFun hS 0) 0
  have h11 := congrFun (congrFun hS 1) 1
  have h01 := congrFun (congrFun hS 0) 1
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h00 h11 h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsMat] <;>
    first | linear_combination h00 / 2 | linear_combination h11 / 2 | exact h01

/-- An actual rank-two skew matrix admits orthonormal source columns and a single
complex coefficient. The construction does not assume equal singular values. -/
theorem exists_orthonormal_skew_factor_of_rank_two {n : Type*} [Fintype n]
    (K : Matrix n n ℂ) (hK : Kᵀ = -K) (hr : K.rank = 2) :
    ∃ (U : Matrix n (Fin 2) ℂ) (z : ℂ),
      Uᴴ * U = 1 ∧ K = z • (U * epsMat * Uᵀ) := by
  classical
  obtain ⟨d, U, B, hd, hU, hUB⟩ := exists_orthonormal_mul K
  rw [hr] at hd
  subst d
  let S : Matrix (Fin 2) (Fin 2) ℂ := Uᴴ * K * Uᵀᴴ
  have hleft : U * Uᴴ * K = K := by
    rw [hUB]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]
  have hright : K * (U * Uᴴ)ᵀ = K := by
    have ht := congrArg Matrix.transpose hleft
    rw [Matrix.transpose_mul, hK, Matrix.neg_mul] at ht
    exact neg_injective ht
  have hUt : (Uᴴ)ᵀ = Uᵀᴴ :=
    (Matrix.conjTranspose_transpose_eq_transpose_conjTranspose U).symm
  have hconj : (Uᵀᴴ)ᵀ = Uᴴ := by rw [← hUt, Matrix.transpose_transpose]
  have hS : Sᵀ = -S := by
    dsimp [S]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hconj, hUt, hK]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hrec : K = U * S * Uᵀ := by
    dsimp [S]
    calc
      K = K * (U * Uᴴ)ᵀ := hright.symm
      _ = (U * Uᴴ * K) * (U * Uᴴ)ᵀ := by rw [hleft]
      _ = U * (Uᴴ * K * Uᵀᴴ) * Uᵀ := by
        rw [Matrix.transpose_mul, hUt]
        simp only [Matrix.mul_assoc]
  refine ⟨U, S 0 1, hU, ?_⟩
  calc
    K = U * S * Uᵀ := hrec
    _ = U * (S 0 1 • epsMat) * Uᵀ := congrArg (fun T => U * T * Uᵀ)
      (skew_fin_two_eq_smul_eps S hS)
    _ = _ := by rw [Matrix.mul_smul, Matrix.smul_mul]

/-- The coefficient's exact norm follows from the original physical Frobenius norm. -/
theorem exists_normalized_orthonormal_skew_factor {n : Type*} [Fintype n]
    (K : Matrix n n ℂ) (hK : Kᵀ = -K) (hr : K.rank = 2) :
    ∃ (U : Matrix n (Fin 2) ℂ) (z : ℂ), Uᴴ * U = 1 ∧
      K = z • (U * epsMat * Uᵀ) ∧ 2 * Complex.normSq z = frobSq K := by
  obtain ⟨U, z, hU, hK⟩ := exists_orthonormal_skew_factor_of_rank_two K hK hr
  refine ⟨U, z, hU, hK, ?_⟩
  rw [hK, frobSq_smul, frobSq_U_eps_Ut U hU]
  ring

end ThreeCopyQutritWerner
