module

public import ThreeCopyQutritWerner.BinarySpinAdjoint
public import ThreeCopyQutritWerner.QutritFamilySiteInvariant
public import ThreeCopyQutritWerner.ZeroFamilies

@[expose] public section


/-! Adjoint invariance of the exact original phased family union. The
two-site spin sign is retained as an allowed unit phase. -/

noncomputable section
open scoped Matrix Kronecker ComplexConjugate
namespace ThreeCopyQutritWerner

theorem familyIMat_conjTranspose
    (f g : Fin 3 → ℂ) (x y : Fin 3 × Fin 3 → ℂ) :
    (familyIMat f g x y)ᴴ = familyIMat f g y x := by
  simp only [familyIMat, tensor₂_eq_kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_smul, proj_conjTranspose, conjTranspose_ketBra,
    Complex.star_def, Complex.conj_ofReal]

theorem familyII_conjTranspose
    (x y : Fin 3 → ℂ) (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    (familyII x y U V₂ V₃)ᴴ = -familyII y x (epsJ₂ * Uᵀᴴ) V₂ V₃ := by
  rw [familyII, tensor₂_eq_kronecker, Matrix.conjTranspose_kronecker, conjTranspose_ketBra]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    binaryB₂_conjTranspose, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc]
  ext i j
  simp only [familyII, tensor₂, Matrix.kroneckerMap_apply, Matrix.neg_apply, mul_neg]

theorem familyIII_conjTranspose
    (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    (familyIII U V₁ V₂ V₃)ᴴ = familyIII (epsJ₃ * Uᵀᴴ) V₁ V₂ V₃ := by
  simp only [familyIII, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    binaryB₃_conjTranspose, Matrix.mul_assoc]

private theorem adjoint_member_of_all_placements
    (F D : Matrix QutritSites QutritSites ℂ)
    (hF : ∀ i : Fin 3, IsQutritZeroFamilyMember
      (Fᴴ.submatrix (binaryPartitionQutritTuple i).symm (binaryPartitionQutritTuple i).symm))
    (hD : D = F ∨ D = F.submatrix siteEquiv₂.symm siteEquiv₂.symm ∨
      D = F.submatrix siteEquiv₃.symm siteEquiv₃.symm) : IsQutritZeroFamilyMember Dᴴ := by
  rcases hD with rfl | rfl | rfl
  · exact hF 0
  · simpa [Matrix.conjTranspose_submatrix, binaryPartitionQutritTuple] using hF 1
  · simpa [Matrix.conjTranspose_submatrix, binaryPartitionQutritTuple] using hF 2

theorem isQutritZeroFamilyMember_conjTranspose
    (C : Matrix QutritSites QutritSites ℂ) (hC : IsQutritZeroFamilyMember C) :
    IsQutritZeroFamilyMember Cᴴ := by
  obtain ⟨z, hz, D, rfl, hD⟩ := hC
  rw [Matrix.conjTranspose_smul]
  apply binaryPartition_family_member_unit_smul
  · rcases hD with hI | hII | hIII
    · obtain ⟨f, g, x, y, hf, hg, hfg, hx, hy, hplace⟩ := hI
      apply adjoint_member_of_all_placements (familyIMat f g x y) D _ hplace
      intro i
      rw [familyIMat_conjTranspose]
      exact qutrit_familyI_all_placements_member f g y x hf hg hfg hy hx i
    · obtain ⟨x, y, U, V₂, V₃, hx, hy, hU, h₂, h₃, hplace⟩ := hII
      apply adjoint_member_of_all_placements (familyII x y U V₂ V₃) D _ hplace
      intro i
      rw [familyII_conjTranspose]
      change IsQutritZeroFamilyMember
        (-((familyII y x (epsJ₂ * Uᵀᴴ) V₂ V₃).submatrix
          (binaryPartitionQutritTuple i).symm (binaryPartitionQutritTuple i).symm))
      have hm := qutrit_familyII_all_placements_member y x (epsJ₂ * Uᵀᴴ) V₂ V₃
        hy hx (epsJ₂_conjugate_frame_isometry U hU) h₂ h₃ i
      simpa only [neg_one_smul] using
        binaryPartition_family_member_unit_smul _ hm (-1) (by norm_num)
    · obtain ⟨U, V₁, V₂, V₃, hU, h₁, h₂, h₃, rfl⟩ := hIII
      rw [familyIII_conjTranspose]
      exact ⟨1, by norm_num, _, by simp, Or.inr (Or.inr
        ⟨epsJ₃ * Uᵀᴴ, V₁, V₂, V₃, epsJ₃_conjugate_frame_isometry U hU,
          h₁, h₂, h₃, rfl⟩)⟩
  · simpa only [Complex.star_def, Complex.normSq_conj] using hz

theorem isQutritZeroFamilyMember_conjTranspose_iff
    (C : Matrix QutritSites QutritSites ℂ) :
    IsQutritZeroFamilyMember Cᴴ ↔ IsQutritZeroFamilyMember C := by
  refine ⟨fun h => ?_, isQutritZeroFamilyMember_conjTranspose C⟩
  simpa only [Matrix.conjTranspose_conjTranspose] using
    isQutritZeroFamilyMember_conjTranspose Cᴴ h

end ThreeCopyQutritWerner
