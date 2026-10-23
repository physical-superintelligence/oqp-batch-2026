module

public import ThreeCopyQutritWerner.BinaryPartitionClassification
public import ThreeCopyQutritWerner.SingularNuclearTrace

@[expose] public section


/-!
# Literal local embeddings of the classified binary tensors

The local two-column matrices retain their actual qutrit columns. Conjugating
a ket-bra transports its two vectors, and a binary identity becomes exactly
the sum of the two column projectors. Thus the embedded matrices use the
manuscript's original plane/frame definitions.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

namespace ThreeCopyQutritWerner

theorem binaryPartition_isometry_vecNormSq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (x : n → ℂ) :
    vecNormSq (V *ᵥ x) = vecNormSq x := by
  apply Complex.ofReal_injective
  rw [← braket_self, ← braket_self]
  exact singular_braket_isometry V hV x x

theorem binaryPartition_conj_ketBra
    {m n : Type*} [Fintype m] [Fintype n]
    (V : Matrix m n ℂ) (x y : n → ℂ) :
    V * ketBra x y * Vᴴ = ketBra (V *ᵥ x) (V *ᵥ y) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    ketBra, map_sum, map_mul, Complex.star_def, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The actual embedded binary identity is the original two-column plane projector. -/
theorem binaryPartition_two_column_projection (V : Matrix (Fin 3) (Fin 2) ℂ) :
    V * Vᴴ = ketBra (fun i => V i 0) (fun i => V i 0) +
      ketBra (fun i => V i 1) (fun i => V i 1) := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Complex.star_def, ketBra]

theorem binaryPartition_two_column_orthonormal
    (V : Matrix (Fin 3) (Fin 2) ℂ) (hV : Vᴴ * V = 1) :
    vecNormSq (fun i => V i 0) = 1 ∧ vecNormSq (fun i => V i 1) = 1 ∧
      braket (fun i => V i 0) (fun i => V i 1) = 0 := by
  have hc (a b : Fin 2) : braket (fun i => V i a) (fun i => V i b) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) a b := by
    have h := congrFun (congrFun hV a) b
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, braket] using h
  refine ⟨?_, ?_, ?_⟩
  · apply Complex.ofReal_injective
    simpa only [braket_self, Matrix.one_apply_eq, Complex.ofReal_one] using hc 0 0
  · apply Complex.ofReal_injective
    simpa only [braket_self, Matrix.one_apply_eq, Complex.ofReal_one] using hc 1 1
  · simpa using hc 0 1

theorem binaryPartition_embed_tensor
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    embed₃ V₁ V₂ V₃ (A ⊗ₖ B) =
      (V₁ * A * V₁ᴴ) ⊗ₖ ((V₂ ⊗ₖ V₃) * B * (V₂ ⊗ₖ V₃)ᴴ) := by
  rw [embed₃_eq_mul, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

theorem binaryPartition_embed_familyI
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) (x y : (Fin 2 × Fin 2) → ℂ) :
    embed₃ V₁ V₂ V₃
        (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ ketBra x y) =
      familyIMat (fun i => V₁ i 0) (fun i => V₁ i 1)
        ((V₂ ⊗ₖ V₃) *ᵥ x) ((V₂ ⊗ₖ V₃) *ᵥ y) := by
  rw [binaryPartition_embed_tensor, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, binaryPartition_two_column_projection, binaryPartition_conj_ketBra]
  rfl

theorem binaryPartition_embed_familyII
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) (x y : Fin 2 → ℂ)
    (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) :
    embed₃ V₁ V₂ V₃ (ketBra x y ⊗ₖ binaryB₂ U) =
      familyII (V₁ *ᵥ x) (V₁ *ᵥ y) U V₂ V₃ := by
  rw [binaryPartition_embed_tensor, binaryPartition_conj_ketBra]
  rfl

end ThreeCopyQutritWerner
