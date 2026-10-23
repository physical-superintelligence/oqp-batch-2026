module

public import ThreeCopyQutritWerner.BinaryPartitionEmbedding

@[expose] public section


/-!
# Original qutrit family placement after a binary local embedding

These are the same three physical site permutations used in the statement
of IsQutritZeroFamilyMember. Site three uses the actual inverse permutation,
and the known family union retains any original unit complex phase.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

def binaryPartitionQutritTuple (i : Fin 3) :
    (Fin 3 × Fin 3 × Fin 3) ≃ (Fin 3 × Fin 3 × Fin 3) :=
  ![Equiv.refl _, siteEquiv₂, siteEquiv₃] i

theorem binaryPartitionQutritTuple_undo (i : Fin 3)
    (C D : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (he : C.submatrix (binaryPartitionQutritTuple i) (binaryPartitionQutritTuple i) = D) :
    C = D.submatrix (binaryPartitionQutritTuple i).symm
      (binaryPartitionQutritTuple i).symm := by
  ext a b
  have h := congrFun (congrFun he ((binaryPartitionQutritTuple i).symm a))
    ((binaryPartitionQutritTuple i).symm b)
  simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using h

/-- Moving the selected site to the front permutes the original local
isometries in precisely the same order as the original binary matrix. -/
theorem binaryPartition_embed_placement
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ)
    (h₁ : V₁ᴴ * V₁ = 1) (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1)
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) (i : Fin 3) :
    ∃ W₁ W₂ W₃ : Matrix (Fin 3) (Fin 2) ℂ,
      W₁ᴴ * W₁ = 1 ∧ W₂ᴴ * W₂ = 1 ∧ W₃ᴴ * W₃ = 1 ∧
      (embed₃ V₁ V₂ V₃ C).submatrix (binaryPartitionQutritTuple i)
        (binaryPartitionQutritTuple i) =
        embed₃ W₁ W₂ W₃
          (C.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i)) := by
  fin_cases i
  · exact ⟨V₁, V₂, V₃, h₁, h₂, h₃, rfl⟩
  · exact ⟨V₂, V₁, V₃, h₂, h₁, h₃, embed₃_submatrix_siteEquiv₂ V₁ V₂ V₃ C⟩
  · exact ⟨V₃, V₁, V₂, h₃, h₁, h₂, embed₃_submatrix_siteEquiv₃ V₁ V₂ V₃ C⟩

theorem binaryPartition_familyI_placement_member
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) (i : Fin 3)
    (f₁ f₂ : Fin 3 → ℂ) (x y : (Fin 3 × Fin 3) → ℂ)
    (hf₁ : vecNormSq f₁ = 1) (hf₂ : vecNormSq f₂ = 1) (hff : braket f₁ f₂ = 0)
    (hx : vecNormSq x = 1) (hy : vecNormSq y = 1)
    (he : C.submatrix (binaryPartitionQutritTuple i) (binaryPartitionQutritTuple i) =
      familyIMat f₁ f₂ x y) : IsQutritZeroFamilyMember C := by
  refine ⟨1, by norm_num, C, by simp,
    Or.inl ⟨f₁, f₂, x, y, hf₁, hf₂, hff, hx, hy, ?_⟩⟩
  have h := binaryPartitionQutritTuple_undo i C _ he
  fin_cases i
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem binaryPartition_familyII_placement_member
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) (i : Fin 3)
    (x y : Fin 3 → ℂ) (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ)
    (hx : vecNormSq x = 1) (hy : vecNormSq y = 1)
    (hU : Uᴴ * U = 1) (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1)
    (he : C.submatrix (binaryPartitionQutritTuple i) (binaryPartitionQutritTuple i) =
      familyII x y U V₂ V₃) : IsQutritZeroFamilyMember C := by
  refine ⟨1, by norm_num, C, by simp,
    Or.inr (Or.inl ⟨x, y, U, V₂, V₃, hx, hy, hU, h₂, h₃, ?_⟩)⟩
  have h := binaryPartitionQutritTuple_undo i C _ he
  fin_cases i
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem binaryPartition_family_member_unit_smul
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hC : IsQutritZeroFamilyMember C) (z : ℂ) (hz : Complex.normSq z = 1) :
    IsQutritZeroFamilyMember (z • C) := by
  obtain ⟨w, hw, D, hD, hfamily⟩ := hC
  refine ⟨z * w, ?_, D, ?_, hfamily⟩
  · rw [Complex.normSq_mul, hz, hw, one_mul]
  · rw [hD, smul_smul]

end ThreeCopyQutritWerner
