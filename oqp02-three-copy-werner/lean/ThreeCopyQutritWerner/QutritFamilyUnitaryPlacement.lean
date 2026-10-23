module

public import ThreeCopyQutritWerner.QutritFamilyLocalAction
public import ThreeCopyQutritWerner.AppendixCInputs

@[expose] public section


/-! Normalized local-unitary transport in each original physical placement. -/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem qutrit_unitary_mul_frame
    (W : Matrix (Fin 3) (Fin 3) ℂ) (V : Matrix (Fin 3) (Fin 2) ℂ)
    (hW : Wᴴ * W = 1) (hV : Vᴴ * V = 1) : (W * V)ᴴ * (W * V) = 1 := by
  calc
    _ = Vᴴ * (Wᴴ * W) * V := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hW, Matrix.mul_one, hV]

theorem qutrit_unitary_embed_placement
    (W₁ W₂ W₃ : Matrix (Fin 3) (Fin 3) ℂ)
    (h₁ : W₁ᴴ * W₁ = 1) (h₂ : W₂ᴴ * W₂ = 1) (h₃ : W₃ᴴ * W₃ = 1)
    (C : Matrix QutritSites QutritSites ℂ) (i : Fin 3) :
    ∃ U₁ U₂ U₃ : Matrix (Fin 3) (Fin 3) ℂ,
      U₁ᴴ * U₁ = 1 ∧ U₂ᴴ * U₂ = 1 ∧ U₃ᴴ * U₃ = 1 ∧
        (embed₃ W₁ W₂ W₃ C).submatrix (binaryPartitionQutritTuple i)
          (binaryPartitionQutritTuple i) =
          embed₃ U₁ U₂ U₃ (C.submatrix (binaryPartitionQutritTuple i)
            (binaryPartitionQutritTuple i)) := by
  fin_cases i
  · exact ⟨W₁, W₂, W₃, h₁, h₂, h₃, rfl⟩
  · exact ⟨W₂, W₁, W₃, h₂, h₁, h₃, embed₃_submatrix_siteEquiv₂ W₁ W₂ W₃ C⟩
  · exact ⟨W₃, W₁, W₂, h₃, h₁, h₂, embed₃_submatrix_siteEquiv₃ W₁ W₂ W₃ C⟩

theorem qutrit_familyI_placement_unitary_member
    (W₁ W₂ W₃ : Matrix (Fin 3) (Fin 3) ℂ)
    (h₁ : W₁ᴴ * W₁ = 1) (h₂ : W₂ᴴ * W₂ = 1) (h₃ : W₃ᴴ * W₃ = 1)
    (C : Matrix QutritSites QutritSites ℂ) (i : Fin 3)
    (f g : Fin 3 → ℂ) (x y : Fin 3 × Fin 3 → ℂ)
    (hf : vecNormSq f = 1) (hg : vecNormSq g = 1) (hfg : braket f g = 0)
    (hx : vecNormSq x = 1) (hy : vecNormSq y = 1)
    (he : C.submatrix (binaryPartitionQutritTuple i) (binaryPartitionQutritTuple i) =
      familyIMat f g x y) : IsQutritZeroFamilyMember (embed₃ W₁ W₂ W₃ C) := by
  obtain ⟨U₁, U₂, U₃, hu₁, hu₂, hu₃, hplace⟩ :=
    qutrit_unitary_embed_placement W₁ W₂ W₃ h₁ h₂ h₃ C i
  apply binaryPartition_familyI_placement_member _ i (U₁ *ᵥ f) (U₁ *ᵥ g)
    ((U₂ ⊗ₖ U₃) *ᵥ x) ((U₂ ⊗ₖ U₃) *ᵥ y)
    ((binaryPartition_isometry_vecNormSq U₁ hu₁ f).trans hf)
    ((binaryPartition_isometry_vecNormSq U₁ hu₁ g).trans hg)
    ((singular_braket_isometry U₁ hu₁ f g).trans hfg)
    ((binaryPartition_isometry_vecNormSq _ (kron_isometry U₂ U₃ hu₂ hu₃) x).trans hx)
    ((binaryPartition_isometry_vecNormSq _ (kron_isometry U₂ U₃ hu₂ hu₃) y).trans hy)
  rw [hplace, he, qutrit_embed_familyI]

theorem qutrit_familyII_placement_unitary_member
    (W₁ W₂ W₃ : Matrix (Fin 3) (Fin 3) ℂ)
    (h₁ : W₁ᴴ * W₁ = 1) (h₂ : W₂ᴴ * W₂ = 1) (h₃ : W₃ᴴ * W₃ = 1)
    (C : Matrix QutritSites QutritSites ℂ) (i : Fin 3)
    (x y : Fin 3 → ℂ) (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ)
    (hx : vecNormSq x = 1) (hy : vecNormSq y = 1) (hU : Uᴴ * U = 1)
    (hv₂ : V₂ᴴ * V₂ = 1) (hv₃ : V₃ᴴ * V₃ = 1)
    (he : C.submatrix (binaryPartitionQutritTuple i) (binaryPartitionQutritTuple i) =
      familyII x y U V₂ V₃) : IsQutritZeroFamilyMember (embed₃ W₁ W₂ W₃ C) := by
  obtain ⟨U₁, U₂, U₃, hu₁, hu₂, hu₃, hplace⟩ :=
    qutrit_unitary_embed_placement W₁ W₂ W₃ h₁ h₂ h₃ C i
  apply binaryPartition_familyII_placement_member _ i (U₁ *ᵥ x) (U₁ *ᵥ y)
    U (U₂ * V₂) (U₃ * V₃)
    ((binaryPartition_isometry_vecNormSq U₁ hu₁ x).trans hx)
    ((binaryPartition_isometry_vecNormSq U₁ hu₁ y).trans hy) hU
    (qutrit_unitary_mul_frame U₂ V₂ hu₂ hv₂) (qutrit_unitary_mul_frame U₃ V₃ hu₃ hv₃)
  rw [hplace, he, qutrit_embed_familyII]

theorem qutrit_familyIII_unitary_member
    (W₁ W₂ W₃ : Matrix (Fin 3) (Fin 3) ℂ)
    (h₁ : W₁ᴴ * W₁ = 1) (h₂ : W₂ᴴ * W₂ = 1) (h₃ : W₃ᴴ * W₃ = 1)
    (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hv₁ : V₁ᴴ * V₁ = 1) (hv₂ : V₂ᴴ * V₂ = 1)
    (hv₃ : V₃ᴴ * V₃ = 1) :
    IsQutritZeroFamilyMember (embed₃ W₁ W₂ W₃ (familyIII U V₁ V₂ V₃)) := by
  rw [qutrit_embed_familyIII]
  refine ⟨1, by norm_num, familyIII U (W₁ * V₁) (W₂ * V₂) (W₃ * V₃),
    by simp, Or.inr (Or.inr ?_)⟩
  exact ⟨U, W₁ * V₁, W₂ * V₂, W₃ * V₃, hU,
    qutrit_unitary_mul_frame W₁ V₁ h₁ hv₁, qutrit_unitary_mul_frame W₂ V₂ h₂ hv₂,
    qutrit_unitary_mul_frame W₃ V₃ h₃ hv₃, rfl⟩

end ThreeCopyQutritWerner
