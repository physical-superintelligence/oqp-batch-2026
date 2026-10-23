module

public import ThreeCopyQutritWerner.TwoCutSwap

@[expose] public section


/-!
# Restoring a common binary carrier to original local coordinates

Both original local unitary changes are undone on their corresponding binary
frames. The compressed matrix and its complex phase are preserved exactly.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- A common carrier after actual local unitary conjugation pulls back to
a constructed common carrier of the original matrix. -/
theorem twoCut_binary_carrier_of_local_conj
    (C : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (U V : Matrix (Fin 3) (Fin 3) ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ)
    (K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1)
    (he : (U ⊗ₖ V) * C * (U ⊗ₖ V)ᴴ = (J₁ ⊗ₖ J₂) * K * (J₁ ⊗ₖ J₂)ᴴ) :
    ∃ V₁ V₂ : Matrix (Fin 3) (Fin 2) ℂ,
      ∃ B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      V₁ᴴ * V₁ = 1 ∧ V₂ᴴ * V₂ = 1 ∧
        C = (V₁ ⊗ₖ V₂) * B * (V₁ ⊗ₖ V₂)ᴴ := by
  have hUU : U * Uᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hU
  have hVV : V * Vᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hV
  have h₁ : (Uᴴ * J₁)ᴴ * (Uᴴ * J₁) = 1 := by
    calc
      _ = J₁ᴴ * (U * Uᴴ) * J₁ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, hJ₁]
  have h₂ : (Vᴴ * J₂)ᴴ * (Vᴴ * J₂) = 1 := by
    calc
      _ = J₂ᴴ * (V * Vᴴ) * J₂ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = 1 := by rw [hVV, Matrix.mul_one, hJ₂]
  have hW : (Uᴴ * J₁) ⊗ₖ (Vᴴ * J₂) = (U ⊗ₖ V)ᴴ * (J₁ ⊗ₖ J₂) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  refine ⟨Uᴴ * J₁, Vᴴ * J₂, K, h₁, h₂, ?_⟩
  calc
    C = (U ⊗ₖ V)ᴴ * ((U ⊗ₖ V) * C * (U ⊗ₖ V)ᴴ) * (U ⊗ₖ V) :=
      (twoCut_unitary_conj_recover _ C (kron_isometry U V hU hV)).symm
    _ = (U ⊗ₖ V)ᴴ * ((J₁ ⊗ₖ J₂) * K * (J₁ ⊗ₖ J₂)ᴴ) * (U ⊗ₖ V) := by rw [he]
    _ = ((U ⊗ₖ V)ᴴ * (J₁ ⊗ₖ J₂)) * K * ((U ⊗ₖ V)ᴴ * (J₁ ⊗ₖ J₂))ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    _ = _ := by rw [← hW]

end ThreeCopyQutritWerner
