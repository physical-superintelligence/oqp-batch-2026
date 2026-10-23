module

public import ThreeCopyQutritWerner.RankTwo
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section


/-!
# Actual orthogonal projections are determined by their ranges

These elementary matrix lemmas use the literal column space. They support
alignment of the original projection blocks, without replacing their ranges
by a supplied common support. No classification theorem is assumed.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- An idempotent fixes every matrix whose columns lie in its actual range. -/
theorem matrix_idempotent_mul_eq_of_range_le
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (P : Matrix n n ℂ) (A : Matrix n m ℂ) (hP : P * P = P)
    (hr : LinearMap.range A.mulVecLin ≤ LinearMap.range P.mulVecLin) : P * A = A := by
  ext i j
  have hcol : Aᵀ j ∈ LinearMap.range A.mulVecLin := by
    refine ⟨Pi.single j 1, ?_⟩
    ext k
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  obtain ⟨v, hv⟩ := hr hcol
  have hfix : P *ᵥ (Aᵀ j) = Aᵀ j := by
    rw [← hv]
    change P *ᵥ (P *ᵥ v) = P *ᵥ v
    rw [Matrix.mulVec_mulVec, hP]
  exact congrFun hfix i

/-- Hermitian idempotents with the same original column space are equal. -/
theorem matrix_hermitian_idempotent_eq_of_range_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hr : LinearMap.range P.mulVecLin = LinearMap.range Q.mulVecLin) : P = Q := by
  have hPQ : P * Q = Q := matrix_idempotent_mul_eq_of_range_le P Q hPP hr.symm.le
  have hQP : Q * P = P := matrix_idempotent_mul_eq_of_range_le Q P hQQ hr.le
  have h := congrArg Matrix.conjTranspose hPQ
  rw [Matrix.conjTranspose_mul, hP.eq, hQ.eq, hQP] at h
  exact h

/-- Actual range inclusion and equal rank suffice; no equality of ranges is
an additional premise. -/
theorem matrix_hermitian_idempotent_eq_of_range_le_rank_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hr : LinearMap.range P.mulVecLin ≤ LinearMap.range Q.mulVecLin)
    (hd : Q.rank ≤ P.rank) : P = Q := by
  apply matrix_hermitian_idempotent_eq_of_range_eq P Q hP hQ hPP hQQ
  exact Submodule.eq_of_le_of_finrank_le hr hd

/-- Right restriction with unchanged rank preserves the original range. -/
theorem matrix_range_mul_eq_of_rank_eq
    {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]
    (A : Matrix n m ℂ) (B : Matrix m k ℂ) (h : (A * B).rank = A.rank) :
    LinearMap.range (A * B).mulVecLin = LinearMap.range A.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, rfl⟩
    refine ⟨B *ᵥ v, ?_⟩
    change A *ᵥ (B *ᵥ v) = (A * B) *ᵥ v
    exact Matrix.mulVec_mulVec v A B
  · exact h

end ThreeCopyQutritWerner
