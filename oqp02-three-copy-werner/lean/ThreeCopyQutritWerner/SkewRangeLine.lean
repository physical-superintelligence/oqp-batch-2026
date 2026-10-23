module

public import ThreeCopyQutritWerner.SkewRankTwoNormal
public import ThreeCopyQutritWerner.OrthogonalProjectionRange

@[expose] public section


/-!
# A rank-two skew source determines one complex line

The source is the actual column range. A second ordinary-transpose skew
matrix supported in it is a scalar multiple of the first, with no equal
singular-value, normalization, or chosen frame premise in the final theorem.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Ordinary skew symmetry turns a fixed two-column output support into the
same transpose support on the right and hence one epsilon coefficient. -/
theorem skew_eq_smul_eps_of_two_column_support
    {n : Type*} [Fintype n]
    (U : Matrix n (Fin 2) ℂ) (K : Matrix n n ℂ) (hK : Kᵀ = -K)
    (hleft : U * Uᴴ * K = K) :
    ∃ z : ℂ, K = z • (U * epsMat * Uᵀ) := by
  let S : Matrix (Fin 2) (Fin 2) ℂ := Uᴴ * K * Uᵀᴴ
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
  refine ⟨S 0 1, ?_⟩
  calc
    K = U * S * Uᵀ := hrec
    _ = U * ((S 0 1) • epsMat) * Uᵀ :=
      congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => U * A * Uᵀ)
        (skew_fin_two_eq_smul_eps S hS)
    _ = (S 0 1) • (U * epsMat * Uᵀ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Any skew matrix with range contained in an actual rank-two skew range
is a scalar multiple of that anchor. The zero second matrix is included. -/
theorem skew_eq_smul_of_range_le_rank_two
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : Aᵀ = -A) (hB : Bᵀ = -B) (hr : A.rank = 2)
    (hBA : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin) :
    ∃ z : ℂ, B = z • A := by
  obtain ⟨d, U, R, hd, hU, hUR⟩ := exists_orthonormal_mul A
  rw [hr] at hd
  subst d
  have hleft : U * Uᴴ * A = A := by
    rw [hUR]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]
  have hp : (U * Uᴴ) * (U * Uᴴ) = U * Uᴴ := by
    calc
      _ = U * (Uᴴ * U) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]
  have hAP : LinearMap.range A.mulVecLin ≤ LinearMap.range (U * Uᴴ).mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨A *ᵥ v, ?_⟩
    change (U * Uᴴ) *ᵥ (A *ᵥ v) = A *ᵥ v
    rw [Matrix.mulVec_mulVec, hleft]
  have hleftB := matrix_idempotent_mul_eq_of_range_le (U * Uᴴ) B hp (hBA.trans hAP)
  obtain ⟨a, ha⟩ := skew_eq_smul_eps_of_two_column_support U A hA hleft
  obtain ⟨b, hb⟩ := skew_eq_smul_eps_of_two_column_support U B hB hleftB
  have ha0 : a ≠ 0 := by
    intro hz
    simp only [hz, zero_smul] at ha
    rw [ha] at hr
    simp at hr
  refine ⟨b / a, ?_⟩
  rw [ha, smul_smul, div_mul_cancel₀ _ ha0]
  exact hb

end ThreeCopyQutritWerner
