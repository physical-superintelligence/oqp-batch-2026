module

public import ThreeCopyQutritWerner.OrthogonalProjectionRange

@[expose] public section


/-!
# Actual right factors from column-range inclusion

Finite column preimages construct the right factor. Reindexing the original
rows and columns therefore preserves source inclusion without introducing
an assumed compatible factorization.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Actual column-space inclusion supplies a literal matrix factor. -/
theorem matrix_exists_right_factor_of_range_le
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    (A : Matrix m p ℂ) (B : Matrix m n ℂ)
    (h : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    ∃ R : Matrix n p ℂ, A = B * R := by
  have hc (j : p) : ∃ v : n → ℂ, B *ᵥ v = fun i => A i j := by
    apply h
    refine ⟨Pi.single j 1, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply']
  choose v hv using hc
  refine ⟨fun i j => v j i, ?_⟩
  ext i j
  exact (congrFun (hv j) i).symm

/-- Reindexing physical coordinates transports actual range inclusion. -/
theorem matrix_range_submatrix_equiv_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (e : m ≃ n)
    (h : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    LinearMap.range (A.submatrix e e).mulVecLin ≤
      LinearMap.range (B.submatrix e e).mulVecLin := by
  obtain ⟨R, hR⟩ := matrix_exists_right_factor_of_range_le A B h
  have he : A.submatrix e e = B.submatrix e e * R.submatrix e e := by
    rw [hR, Matrix.submatrix_mul_equiv]
  rw [he]
  rintro _ ⟨v, rfl⟩
  refine ⟨R.submatrix e e *ᵥ v, ?_⟩
  change B.submatrix e e *ᵥ (R.submatrix e e *ᵥ v) =
    (B.submatrix e e * R.submatrix e e) *ᵥ v
  exact Matrix.mulVec_mulVec v _ _

end ThreeCopyQutritWerner
