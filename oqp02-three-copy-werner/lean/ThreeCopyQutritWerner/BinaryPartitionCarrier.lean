module

public import ThreeCopyQutritWerner.BinaryPartitionFamilyPlacement
public import ThreeCopyQutritWerner.ProductRayUnitary

@[expose] public section


/-!
# The original qutrit family conclusion on an actual binary carrier

Every actual normalized binary zero embeds into the original manuscript
family union under arbitrary local qutrit isometries, with all placements
and unit phases included. For a qutrit matrix already on such a carrier,
rank, energy, and normalization are transferred from that original matrix.
Constructing a carrier for an arbitrary thin qutrit zero remains separate.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem binaryPartitionSiteTuple_redo (i : Fin 3)
    (C D : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (he : C = D.submatrix (binaryPartitionSiteTuple i).symm (binaryPartitionSiteTuple i).symm) :
    C.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) = D := by
  rw [he]
  ext a b
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]

/-- Classification of the actual embedded matrix, with the given local
isometries furnishing the planes and vectors in the original family union. -/
theorem binaryPartition_embed_normalized_family_member
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hC : C.rank ≤ 2) (hz : endpointEnergy C = 0) (hN : frobSq C = 1)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ)
    (h₁ : V₁ᴴ * V₁ = 1) (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1) :
    IsQutritZeroFamilyMember (embed₃ V₁ V₂ V₃ C) := by
  rcases binary_endpoint_normalized_three_family_classification C hC hz hN with h | h | h
  · obtain ⟨i, x, y, hx, hy, hnormal⟩ := h
    obtain ⟨W₁, W₂, W₃, hW₁, hW₂, hW₃, he⟩ :=
      binaryPartition_embed_placement V₁ V₂ V₃ h₁ h₂ h₃ C i
    rw [binaryPartitionSiteTuple_redo i C _ hnormal, binaryPartition_embed_familyI] at he
    obtain ⟨hf₁, hf₂, hff⟩ := binaryPartition_two_column_orthonormal W₁ hW₁
    have hW := kron_isometry W₂ W₃ hW₂ hW₃
    exact binaryPartition_familyI_placement_member _ i _ _ _ _ hf₁ hf₂ hff
      ((binaryPartition_isometry_vecNormSq _ hW x).trans hx)
      ((binaryPartition_isometry_vecNormSq _ hW y).trans hy) he
  · obtain ⟨i, x, y, U, hx, hy, hU, hnormal⟩ := h
    obtain ⟨W₁, W₂, W₃, hW₁, hW₂, hW₃, he⟩ :=
      binaryPartition_embed_placement V₁ V₂ V₃ h₁ h₂ h₃ C i
    rw [binaryPartitionSiteTuple_redo i C _ hnormal, binaryPartition_embed_familyII] at he
    exact binaryPartition_familyII_placement_member _ i _ _ U W₂ W₃
      ((binaryPartition_isometry_vecNormSq W₁ hW₁ x).trans hx)
      ((binaryPartition_isometry_vecNormSq W₁ hW₁ y).trans hy) hU hW₂ hW₃ he
  · obtain ⟨U, hU, hnormal⟩ := h
    refine ⟨1, by norm_num, embed₃ V₁ V₂ V₃ C, by simp,
      Or.inr (Or.inr ⟨U, V₁, V₂, V₃, hU, h₁, h₂, h₃, ?_⟩)⟩
    rw [hnormal, familyIII_eq_embed₃]

/-- Any original unit phase remains in the stated family union. -/
theorem binaryPartition_embed_unit_phase_family_member
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hC : C.rank ≤ 2) (hz : endpointEnergy C = 0) (hN : frobSq C = 1)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ)
    (h₁ : V₁ᴴ * V₁ = 1) (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1)
    (z : ℂ) (hphase : Complex.normSq z = 1) :
    IsQutritZeroFamilyMember (z • embed₃ V₁ V₂ V₃ C) :=
  binaryPartition_family_member_unit_smul _
    (binaryPartition_embed_normalized_family_member C hC hz hN V₁ V₂ V₃ h₁ h₂ h₃) z hphase

/-- On an actual supplied binary carrier, the original qutrit assumptions
alone imply the original qutrit family conclusion. No binary rank, energy,
or normalization premise is added for the compressed matrix. -/
theorem binaryPartition_qutrit_family_of_binary_carrier
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hC : C.rank ≤ 2) (hz : endpointEnergy C = 0) (hN : frobSq C = 1)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ)
    (h₁ : V₁ᴴ * V₁ = 1) (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1)
    (K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (he : C = embed₃ V₁ V₂ V₃ K) : IsQutritZeroFamilyMember C := by
  have hrK : K.rank ≤ 2 := by
    simpa only [he, productRay_rank_embed₃ h₁ h₂ h₃] using hC
  have hzK : endpointEnergy K = 0 := by
    simpa only [he, productRay_endpointEnergy_embed₃ h₁ h₂ h₃] using hz
  have hNK : frobSq K = 1 := by
    simpa only [he, frobSq_embed₃ h₁ h₂ h₃] using hN
  rw [he]
  exact binaryPartition_embed_normalized_family_member K hrK hzK hNK V₁ V₂ V₃ h₁ h₂ h₃

end ThreeCopyQutritWerner
