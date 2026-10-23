module

public import ThreeCopyQutritWerner.QutritThinFrame
public import ThreeCopyQutritWerner.CoherentPencilSupport
public import ThreeCopyQutritWerner.BinaryZeros

@[expose] public section


/-!
# Constructed physical support frames from the manuscript's local ranks

The support hypothesis is the original rank of a partial trace of CC†.
It supplies a concrete binary isometry on that physical site fixing C on
the left. This does not assert a common output/input plane or a binary
carrier at all three sites.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- A thin first local range gives an actual first-site binary frame. -/
theorem localRangeDim₁_le_two_exists_frame
    (C : Matrix QutritSites QutritSites ℂ) (h : localRangeDim₁ C ≤ 2) :
    ∃ J : Matrix (Fin 3) (Fin 2) ℂ, Jᴴ * J = 1 ∧
      (J ⊗ₖ (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)) *
        (J ⊗ₖ (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ))ᴴ * C = C := by
  rw [localRangeDim₁_eq_coherentFlatten_rank] at h
  obtain ⟨J, hJ, hfix⟩ := qutrit_rank_le_two_exists_binary_frame (coherentFlatten₁ C) h
  refine ⟨J, hJ, ?_⟩
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext ⟨i, j, k⟩ q
  have he := congrFun (congrFun hfix i) ((j, k), q)
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, coherentFlatten₁, ite_mul, mul_ite, Prod.mk.injEq] using he

/-- The second-site frame is in the original physical tuple order. -/
theorem localRangeDim₂_le_two_exists_frame
    (C : Matrix QutritSites QutritSites ℂ) (h : localRangeDim₂ C ≤ 2) :
    ∃ J : Matrix (Fin 3) (Fin 2) ℂ, Jᴴ * J = 1 ∧
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ (J ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))) *
        ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ (J ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)))ᴴ * C = C := by
  rw [localRangeDim₂_eq_coherentFlatten_rank] at h
  obtain ⟨J, hJ, hfix⟩ := qutrit_rank_le_two_exists_binary_frame (coherentFlatten₂ C) h
  refine ⟨J, hJ, ?_⟩
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext ⟨i, j, k⟩ q
  have he := congrFun (congrFun hfix j) ((i, k), q)
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, coherentFlatten₂, ite_mul, mul_ite] using he

/-- The third-site frame is also constructed from the literal local rank. -/
theorem localRangeDim₃_le_two_exists_frame
    (C : Matrix QutritSites QutritSites ℂ) (h : localRangeDim₃ C ≤ 2) :
    ∃ J : Matrix (Fin 3) (Fin 2) ℂ, Jᴴ * J = 1 ∧
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ J)) *
        ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ J))ᴴ * C = C := by
  rw [localRangeDim₃_eq_coherentFlatten_rank] at h
  obtain ⟨J, hJ, hfix⟩ := qutrit_rank_le_two_exists_binary_frame (coherentFlatten₃ C) h
  refine ⟨J, hJ, ?_⟩
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext ⟨i, j, k⟩ q
  have he := congrFun (congrFun hfix k) ((i, j), q)
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, coherentFlatten₃, ite_mul, mul_ite] using he

/-- Compressing into an actual isometric output frame preserves the original
rank and squared Frobenius norm, without an input-support assumption. -/
theorem isometric_output_compression_rank_norm
    {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq k]
    (C : Matrix m n ℂ) (K : Matrix m k ℂ)
    (hK : Kᴴ * K = 1) (hfix : K * Kᴴ * C = C) :
    (Kᴴ * C).rank = C.rank ∧ frobSq (Kᴴ * C) = frobSq C := by
  have he : K * (Kᴴ * C) = C := by rwa [← Matrix.mul_assoc]
  constructor
  · apply le_antisymm (Matrix.rank_mul_le_right _ _)
    calc
      C.rank = (K * (Kᴴ * C)).rank := congrArg Matrix.rank he.symm
      _ ≤ (Kᴴ * C).rank := Matrix.rank_mul_le_right _ _
  · have hn := frobSq_isometry_mul K hK (Kᴴ * C)
    rw [he] at hn
    exact hn.symm

end ThreeCopyQutritWerner
