module

public import ThreeCopyQutritWerner.MatrixRangeFactor
public import ThreeCopyQutritWerner.TwoCutSingleOutputFactor

@[expose] public section


/-!
# The orthogonal projection is fixed by a tensor source

An actual range inclusion transports any left stabilizer. For nonzero
Kronecker first factors, cancellation then identifies the second-site
orthogonal projections of equal rank. Arbitrary complex first factors are
retained; they need not have matching right vectors or phases.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Every left stabilizer of an actual source stabilizes its subspaces. -/
theorem matrix_left_stabilizer_of_range_le
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    (P : Matrix m m ℂ) (A : Matrix m n ℂ) (B : Matrix m p ℂ)
    (hPA : P * A = A)
    (hBA : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin) : P * B = B := by
  obtain ⟨R, hR⟩ := matrix_exists_right_factor_of_range_le B A hBA
  rw [hR, ← Matrix.mul_assoc, hPA]

/-- The actual tensor source identifies the orthogonal second-site
projection. A nonzero arbitrary first factor suffices for cancellation. -/
theorem orthogonal_projection_eq_of_kronecker_range_le
    {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a] [DecidableEq d]
    (M N : Matrix a a ℂ) (P Q : Matrix d d ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hr : P.rank ≤ Q.rank) (hN : N ≠ 0)
    (hR : LinearMap.range (N ⊗ₖ Q).mulVecLin ≤ LinearMap.range (M ⊗ₖ P).mulVecLin) :
    P = Q := by
  classical
  have hfix : ((1 : Matrix a a ℂ) ⊗ₖ P) * (M ⊗ₖ P) = M ⊗ₖ P := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hPP]
  have hB := matrix_left_stabilizer_of_range_le _ _ _ hfix hR
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul] at hB
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hN (Matrix.ext h)
  have hPQ : P * Q = Q := by
    ext r s
    have he := congrFun (congrFun hB (i, r)) (j, s)
    simp only [Matrix.kroneckerMap_apply] at he
    exact mul_left_cancel₀ hij he
  have hQP : LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨Q *ᵥ v, ?_⟩
    change P *ᵥ (Q *ᵥ v) = Q *ᵥ v
    rw [Matrix.mulVec_mulVec, hPQ]
  exact (matrix_hermitian_idempotent_eq_of_range_le_rank_le Q P hQ hP hQQ hPP hQP hr).symm

end ThreeCopyQutritWerner
