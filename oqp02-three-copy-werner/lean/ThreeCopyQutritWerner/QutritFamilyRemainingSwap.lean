module

public import ThreeCopyQutritWerner.FamilyIIIPlacement
public import ThreeCopyQutritWerner.TwoCutSwap

@[expose] public section


/-! Literal exchange of the two inactive sites in the original families.
The arbitrary family-I vectors are only reindexed, never restricted to a
binary carrier. -/

noncomputable section
open scoped Matrix Kronecker
namespace ThreeCopyQutritWerner

def qutritRemainingSwap : (Fin 3 × Fin 3 × Fin 3) ≃ (Fin 3 × Fin 3 × Fin 3) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)

theorem familyIMat_remaining_swap
    (f g : Fin 3 → ℂ) (x y : Fin 3 × Fin 3 → ℂ) :
    (familyIMat f g x y).submatrix qutritRemainingSwap qutritRemainingSwap =
      familyIMat f g (x ∘ Equiv.prodComm _ _) (y ∘ Equiv.prodComm _ _) := by
  rfl

theorem binaryB₂_submatrix_of_spin
    (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
    (e : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (he : epsJ₂ᵀ.submatrix e e = epsJ₂ᵀ) :
    (binaryB₂ U).submatrix e e = binaryB₂ (U.submatrix e id) := by
  have h₁ : (U * epsMat).submatrix e id = U.submatrix e id * epsMat := by
    simpa using (Matrix.submatrix_mul_equiv U epsMat e (Equiv.refl (Fin 2)) id).symm
  have h₂ : (U * epsMat * Uᵀ).submatrix e e =
      U.submatrix e id * epsMat * (U.submatrix e id)ᵀ := by
    calc
      _ = (U * epsMat).submatrix e id * Uᵀ.submatrix id e :=
        (Matrix.submatrix_mul_equiv (U * epsMat) Uᵀ e (Equiv.refl (Fin 2)) e).symm
      _ = _ := by rw [h₁, Matrix.transpose_submatrix]
  have h₃ : (U * epsMat * Uᵀ * epsJ₂ᵀ).submatrix e e =
      (U.submatrix e id * epsMat * (U.submatrix e id)ᵀ) * epsJ₂ᵀ := by
    calc
      _ = (U * epsMat * Uᵀ).submatrix e e * epsJ₂ᵀ.submatrix e e :=
        (Matrix.submatrix_mul_equiv (U * epsMat * Uᵀ) epsJ₂ᵀ e e e).symm
      _ = _ := by rw [h₂, he]
  simpa only [binaryB₂, epsJ₂_inv, Matrix.submatrix_smul, Pi.smul_apply] using
    congrArg (fun M => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • M) h₃

theorem binaryB₂_twoCutSwap (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) :
    twoCutSwap (binaryB₂ U) = binaryB₂ (U.submatrix (Equiv.prodComm _ _) id) := by
  apply binaryB₂_submatrix_of_spin
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply, epsJ₂,
    Matrix.kroneckerMap_apply, Equiv.prodComm_apply, Prod.swap]
  ring

theorem familyII_remaining_swap
    (x y : Fin 3 → ℂ) (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    (familyII x y U V₂ V₃).submatrix qutritRemainingSwap qutritRemainingSwap =
      familyII x y (U.submatrix (Equiv.prodComm _ _) id) V₃ V₂ := by
  have he := twoCutSwap_binary_embedding V₂ V₃ (binaryB₂ U)
  rw [binaryB₂_twoCutSwap] at he
  ext i j
  exact congrArg (fun K => ketBra x y i.1 j.1 * K i.2 j.2) he

end ThreeCopyQutritWerner
