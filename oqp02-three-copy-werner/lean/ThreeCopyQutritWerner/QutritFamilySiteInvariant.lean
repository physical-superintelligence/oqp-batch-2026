module

public import ThreeCopyQutritWerner.QutritFamilyRemainingSwap
public import ThreeCopyQutritWerner.QutritFamilyUnitaryInvariant
public import ThreeCopyQutritWerner.InteriorReduction

@[expose] public section


/-! Invariance of the exact original family union under the physical site
permutations. The inactive-site swaps are absorbed in the original parameters. -/

noncomputable section
open scoped Matrix
namespace ThreeCopyQutritWerner

private theorem member_reindex_of_all_placements
    (F D : Matrix QutritSites QutritSites ℂ)
    (hF : ∀ i : Fin 3, IsQutritZeroFamilyMember
      (F.submatrix (binaryPartitionQutritTuple i).symm (binaryPartitionQutritTuple i).symm))
    (hG : ∀ i : Fin 3, IsQutritZeroFamilyMember
      ((F.submatrix qutritRemainingSwap qutritRemainingSwap).submatrix
        (binaryPartitionQutritTuple i).symm (binaryPartitionQutritTuple i).symm))
    (hD : D = F ∨ D = F.submatrix siteEquiv₂.symm siteEquiv₂.symm ∨
      D = F.submatrix siteEquiv₃.symm siteEquiv₃.symm) (i : Fin 3) :
    IsQutritZeroFamilyMember
      (D.submatrix (binaryPartitionQutritTuple i) (binaryPartitionQutritTuple i)) := by
  rcases hD with rfl | rfl | rfl
  · fin_cases i
    · exact hF 0
    · exact hF 1
    · exact hG 1
  · fin_cases i
    · exact hF 1
    · exact hF 0
    · exact hG 2
  · fin_cases i
    · exact hF 2
    · exact hG 2
    · exact hF 0

theorem qutrit_familyI_all_placements_member
    (f g : Fin 3 → ℂ) (x y : Fin 3 × Fin 3 → ℂ)
    (hf : vecNormSq f = 1) (hg : vecNormSq g = 1) (hfg : braket f g = 0)
    (hx : vecNormSq x = 1) (hy : vecNormSq y = 1) (i : Fin 3) :
    IsQutritZeroFamilyMember ((familyIMat f g x y).submatrix
      (binaryPartitionQutritTuple i).symm (binaryPartitionQutritTuple i).symm) := by
  apply binaryPartition_familyI_placement_member _ i f g x y hf hg hfg hx hy
  ext a b
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem qutrit_familyII_all_placements_member
    (x y : Fin 3 → ℂ) (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ)
    (hx : vecNormSq x = 1) (hy : vecNormSq y = 1) (hU : Uᴴ * U = 1)
    (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1) (i : Fin 3) :
    IsQutritZeroFamilyMember ((familyII x y U V₂ V₃).submatrix
      (binaryPartitionQutritTuple i).symm (binaryPartitionQutritTuple i).symm) := by
  apply binaryPartition_familyII_placement_member _ i x y U V₂ V₃ hx hy hU h₂ h₃
  ext a b
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem qutrit_familyIII_reindex_member
    (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
    (h₁ : V₁ᴴ * V₁ = 1) (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1) (i : Fin 3) :
    IsQutritZeroFamilyMember ((familyIII U V₁ V₂ V₃).submatrix
      (binaryPartitionQutritTuple i) (binaryPartitionQutritTuple i)) := by
  have hmember (W : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
      (J₁ J₂ J₃ : Matrix (Fin 3) (Fin 2) ℂ)
      (hW : Wᴴ * W = 1) (hj₁ : J₁ᴴ * J₁ = 1)
      (hj₂ : J₂ᴴ * J₂ = 1) (hj₃ : J₃ᴴ * J₃ = 1) :
      IsQutritZeroFamilyMember (familyIII W J₁ J₂ J₃) :=
    ⟨1, by norm_num, _, by simp, Or.inr (Or.inr ⟨W, J₁, J₂, J₃,
      hW, hj₁, hj₂, hj₃, rfl⟩)⟩
  fin_cases i
  · exact hmember U V₁ V₂ V₃ hU h₁ h₂ h₃
  · change IsQutritZeroFamilyMember ((familyIII U V₁ V₂ V₃).submatrix siteEquiv₂ siteEquiv₂)
    rw [familyIII_submatrix_site₂]
    exact hmember _ V₂ V₁ V₃ (isometry_submatrix_rows_equiv U hU _) h₂ h₁ h₃
  · change IsQutritZeroFamilyMember ((familyIII U V₁ V₂ V₃).submatrix siteEquiv₃ siteEquiv₃)
    rw [familyIII_submatrix_site₃]
    exact hmember _ V₃ V₁ V₂ (isometry_submatrix_rows_equiv U hU _) h₃ h₁ h₂

theorem isQutritZeroFamilyMember_site
    (C : Matrix QutritSites QutritSites ℂ) (hC : IsQutritZeroFamilyMember C) (i : Fin 3) :
    IsQutritZeroFamilyMember
      (C.submatrix (binaryPartitionQutritTuple i) (binaryPartitionQutritTuple i)) := by
  obtain ⟨z, hz, D, rfl, hD⟩ := hC
  rw [Matrix.submatrix_smul]
  apply binaryPartition_family_member_unit_smul _ _ z hz
  rcases hD with hI | hII | hIII
  · obtain ⟨f, g, x, y, hf, hg, hfg, hx, hy, hplace⟩ := hI
    apply member_reindex_of_all_placements (familyIMat f g x y) D
      (qutrit_familyI_all_placements_member f g x y hf hg hfg hx hy) _ hplace i
    intro j
    rw [familyIMat_remaining_swap]
    exact qutrit_familyI_all_placements_member f g _ _ hf hg hfg
      ((vecNormSq_comp_equiv _ x).trans hx) ((vecNormSq_comp_equiv _ y).trans hy) j
  · obtain ⟨x, y, U, V₂, V₃, hx, hy, hU, h₂, h₃, hplace⟩ := hII
    apply member_reindex_of_all_placements (familyII x y U V₂ V₃) D
      (qutrit_familyII_all_placements_member x y U V₂ V₃ hx hy hU h₂ h₃) _ hplace i
    intro j
    rw [familyII_remaining_swap]
    exact qutrit_familyII_all_placements_member x y _ V₃ V₂ hx hy
      (isometry_submatrix_rows_equiv U hU _) h₃ h₂ j
  · obtain ⟨U, V₁, V₂, V₃, hU, h₁, h₂, h₃, rfl⟩ := hIII
    exact qutrit_familyIII_reindex_member U V₁ V₂ V₃ hU h₁ h₂ h₃ i

theorem isQutritZeroFamilyMember_site_iff
    (C : Matrix QutritSites QutritSites ℂ) (i : Fin 3) :
    IsQutritZeroFamilyMember
      (C.submatrix (binaryPartitionQutritTuple i) (binaryPartitionQutritTuple i)) ↔
        IsQutritZeroFamilyMember C := by
  refine ⟨?_, fun h => isQutritZeroFamilyMember_site C h i⟩
  intro h
  fin_cases i
  · exact h
  · exact isQutritZeroFamilyMember_site _ h 1
  · exact isQutritZeroFamilyMember_site _ (isQutritZeroFamilyMember_site _ h 2) 2

end ThreeCopyQutritWerner
