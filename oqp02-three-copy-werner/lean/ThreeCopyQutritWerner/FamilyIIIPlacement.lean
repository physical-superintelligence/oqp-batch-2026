module

public import ThreeCopyQutritWerner.BinaryPartitionSpin
public import ThreeCopyQutritWerner.BinaryZeros

@[expose] public section


/-!
# Literal site covariance of family III

The three identical epsilon factors are invariant under the physical site
permutations. Reindexing the rows of the actual two-column frame therefore
reindexes the original binary spin form, preserving its orthonormality.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Ordinary-transpose spin covariance under an actual index
permutation preserving the fixed spin matrix. -/
theorem binaryB₃_submatrix_of_spin
    (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (e : (Fin 2 × Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2 × Fin 2))
    (he : epsJ₃ᵀ.submatrix e e = epsJ₃ᵀ) :
    (binaryB₃ U).submatrix e e = binaryB₃ (U.submatrix e id) := by
  have h₁ : (U * epsMat).submatrix e id = U.submatrix e id * epsMat := by
    simpa using (Matrix.submatrix_mul_equiv U epsMat e (Equiv.refl (Fin 2)) id).symm
  have h₂ : (U * epsMat * Uᵀ).submatrix e e =
      U.submatrix e id * epsMat * (U.submatrix e id)ᵀ := by
    calc
      _ = (U * epsMat).submatrix e id * Uᵀ.submatrix id e :=
        (Matrix.submatrix_mul_equiv (U * epsMat) Uᵀ e (Equiv.refl (Fin 2)) e).symm
      _ = _ := by rw [h₁, Matrix.transpose_submatrix]
  have h₃ : (U * epsMat * Uᵀ * epsJ₃ᵀ).submatrix e e =
      (U.submatrix e id * epsMat * (U.submatrix e id)ᵀ) * epsJ₃ᵀ := by
    calc
      _ = (U * epsMat * Uᵀ).submatrix e e * epsJ₃ᵀ.submatrix e e :=
        (Matrix.submatrix_mul_equiv (U * epsMat * Uᵀ) epsJ₃ᵀ e e e).symm
      _ = _ := by rw [h₂, he]
  simpa only [binaryB₃, epsJ₃_inv, Matrix.submatrix_smul, Pi.smul_apply] using
    congrArg (fun M => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • M) h₃

/-- Reindexing rows of an actual isometry preserves the literal Gram equation. -/
theorem isometry_submatrix_rows_equiv {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq k]
    (U : Matrix n k ℂ) (hU : Uᴴ * U = 1) (e : n ≃ n) :
    (U.submatrix e id)ᴴ * U.submatrix e id = 1 := by
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv Uᴴ U id e id, hU]
  rfl

theorem familyIII_submatrix_site₂
    (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    (familyIII U V₁ V₂ V₃).submatrix siteEquiv₂ siteEquiv₂ =
      familyIII (U.submatrix siteEquiv₂ id) V₂ V₁ V₃ := by
  have hspin : epsJ₃ᵀ.submatrix siteEquiv₂ siteEquiv₂ = epsJ₃ᵀ := by
    simpa [binaryPartitionSiteTuple] using binaryPartitionSiteTuple_spin_transpose 1
  rw [familyIII_eq_embed₃, embed₃_submatrix_siteEquiv₂,
    binaryB₃_submatrix_of_spin U siteEquiv₂ hspin, familyIII_eq_embed₃]

theorem familyIII_submatrix_site₃
    (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    (familyIII U V₁ V₂ V₃).submatrix siteEquiv₃ siteEquiv₃ =
      familyIII (U.submatrix siteEquiv₃ id) V₃ V₁ V₂ := by
  have hspin : epsJ₃ᵀ.submatrix siteEquiv₃ siteEquiv₃ = epsJ₃ᵀ := by
    simpa [binaryPartitionSiteTuple] using binaryPartitionSiteTuple_spin_transpose 2
  rw [familyIII_eq_embed₃, embed₃_submatrix_siteEquiv₃,
    binaryB₃_submatrix_of_spin U siteEquiv₃ hspin, familyIII_eq_embed₃]

/-- The site-three placement in Basic uses the inverse cycle. -/
theorem familyIII_submatrix_site₃_symm
    (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    (familyIII U V₁ V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm =
      familyIII (U.submatrix siteEquiv₃.symm id) V₂ V₃ V₁ := by
  calc
    _ = ((familyIII U V₁ V₂ V₃).submatrix siteEquiv₃ siteEquiv₃).submatrix
        siteEquiv₃ siteEquiv₃ := by ext i j; rfl
    _ = familyIII ((U.submatrix siteEquiv₃ id).submatrix siteEquiv₃ id) V₂ V₃ V₁ := by
      rw [familyIII_submatrix_site₃, familyIII_submatrix_site₃]
    _ = _ := by rfl

end ThreeCopyQutritWerner
