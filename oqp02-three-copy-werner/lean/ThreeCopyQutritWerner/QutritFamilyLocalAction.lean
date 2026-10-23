module

public import ThreeCopyQutritWerner.BinaryPartitionFamilyPlacement

@[expose] public section


/-!
# Literal local conjugation of the three original qutrit families

These identities transport the actual defining vectors and physical frames.
They require no unitarity: normalization is checked separately when using
them to preserve membership in the family union.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

variable (W₁ W₂ W₃ : Matrix (Fin 3) (Fin 3) ℂ)

theorem qutrit_embed_tensor
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    embed₃ W₁ W₂ W₃ (A ⊗ₖ B) =
      (W₁ * A * W₁ᴴ) ⊗ₖ ((W₂ ⊗ₖ W₃) * B * (W₂ ⊗ₖ W₃)ᴴ) := by
  rw [embed₃_eq_mul, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

theorem qutrit_embed_familyI (f g : Fin 3 → ℂ) (x y : Fin 3 × Fin 3 → ℂ) :
    embed₃ W₁ W₂ W₃ (familyIMat f g x y) =
      familyIMat (W₁ *ᵥ f) (W₁ *ᵥ g) ((W₂ ⊗ₖ W₃) *ᵥ x) ((W₂ ⊗ₖ W₃) *ᵥ y) := by
  simp only [familyIMat, tensor₂_eq_kronecker, qutrit_embed_tensor,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    binaryPartition_conj_ketBra]

theorem qutrit_embed_familyII (x y : Fin 3 → ℂ)
    (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    embed₃ W₁ W₂ W₃ (familyII x y U V₂ V₃) =
      familyII (W₁ *ᵥ x) (W₁ *ᵥ y) U (W₂ * V₂) (W₃ * V₃) := by
  simp only [familyII, tensor₂_eq_kronecker]
  rw [qutrit_embed_tensor, binaryPartition_conj_ketBra]
  simp only [Matrix.mul_kronecker_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem qutrit_embed_familyIII
    (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    embed₃ W₁ W₂ W₃ (familyIII U V₁ V₂ V₃) =
      familyIII U (W₁ * V₁) (W₂ * V₂) (W₃ * V₃) := by
  rw [embed₃_eq_mul]
  simp only [familyIII, Matrix.mul_kronecker_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

end ThreeCopyQutritWerner
