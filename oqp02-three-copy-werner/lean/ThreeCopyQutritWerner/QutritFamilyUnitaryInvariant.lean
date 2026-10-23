module

public import ThreeCopyQutritWerner.QutritFamilyUnitaryPlacement
public import ThreeCopyQutritWerner.TwoCutLocalConjugation

@[expose] public section


/-!
# The family union is invariant under actual local unitaries

Every original placement and unit phase is retained. The inverse is the
literal adjoint conjugation, so a classification proved in constructed
local coordinates returns to the original operator without a new premise.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem qutrit_family_placement_exists
    (C F : Matrix QutritSites QutritSites ℂ)
    (h : C = F ∨ C = F.submatrix siteEquiv₂.symm siteEquiv₂.symm ∨
      C = F.submatrix siteEquiv₃.symm siteEquiv₃.symm) :
    ∃ i : Fin 3, C.submatrix (binaryPartitionQutritTuple i)
      (binaryPartitionQutritTuple i) = F := by
  rcases h with h | h | h
  · refine ⟨0, ?_⟩
    rw [h]
    rfl
  · refine ⟨1, ?_⟩
    rw [h]
    rfl
  · refine ⟨2, ?_⟩
    rw [h]
    rfl

theorem isQutritZeroFamilyMember_local_unitary
    (W₁ W₂ W₃ : Matrix (Fin 3) (Fin 3) ℂ)
    (h₁ : W₁ᴴ * W₁ = 1) (h₂ : W₂ᴴ * W₂ = 1) (h₃ : W₃ᴴ * W₃ = 1)
    (C : Matrix QutritSites QutritSites ℂ) (hC : IsQutritZeroFamilyMember C) :
    IsQutritZeroFamilyMember (embed₃ W₁ W₂ W₃ C) := by
  obtain ⟨z, hz, D, he, hD⟩ := hC
  have htrans : IsQutritZeroFamilyMember (embed₃ W₁ W₂ W₃ D) := by
    rcases hD with hI | hII | hIII
    · obtain ⟨f, g, x, y, hf, hg, hfg, hx, hy, hplace⟩ := hI
      obtain ⟨i, hi⟩ := qutrit_family_placement_exists D _ hplace
      exact qutrit_familyI_placement_unitary_member W₁ W₂ W₃ h₁ h₂ h₃
        D i f g x y hf hg hfg hx hy hi
    · obtain ⟨x, y, U, V₂, V₃, hx, hy, hU, hv₂, hv₃, hplace⟩ := hII
      obtain ⟨i, hi⟩ := qutrit_family_placement_exists D _ hplace
      exact qutrit_familyII_placement_unitary_member W₁ W₂ W₃ h₁ h₂ h₃
        D i x y U V₂ V₃ hx hy hU hv₂ hv₃ hi
    · obtain ⟨U, V₁, V₂, V₃, hU, hv₁, hv₂, hv₃, hform⟩ := hIII
      rw [hform]
      exact qutrit_familyIII_unitary_member W₁ W₂ W₃ h₁ h₂ h₃ U V₁ V₂ V₃
        hU hv₁ hv₂ hv₃
  have hscale : embed₃ W₁ W₂ W₃ C = z • embed₃ W₁ W₂ W₃ D := by
    simp only [he, embed₃_eq_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hscale]
  exact binaryPartition_family_member_unit_smul _ htrans z hz

theorem qutrit_unitary_embed_recover
    (W₁ W₂ W₃ : Matrix (Fin 3) (Fin 3) ℂ)
    (h₁ : W₁ᴴ * W₁ = 1) (h₂ : W₂ᴴ * W₂ = 1) (h₃ : W₃ᴴ * W₃ = 1)
    (C : Matrix QutritSites QutritSites ℂ) :
    embed₃ W₁ᴴ W₂ᴴ W₃ᴴ (embed₃ W₁ W₂ W₃ C) = C := by
  simp only [embed₃_eq_mul, ← Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose]
  exact twoCut_unitary_conj_recover _ C (kron₃_isometry h₁ h₂ h₃)

theorem isQutritZeroFamilyMember_local_unitary_iff
    (W₁ W₂ W₃ : Matrix (Fin 3) (Fin 3) ℂ)
    (h₁ : W₁ᴴ * W₁ = 1) (h₂ : W₂ᴴ * W₂ = 1) (h₃ : W₃ᴴ * W₃ = 1)
    (C : Matrix QutritSites QutritSites ℂ) :
    IsQutritZeroFamilyMember (embed₃ W₁ W₂ W₃ C) ↔ IsQutritZeroFamilyMember C := by
  constructor
  · intro h
    have hu₁ : (W₁ᴴ)ᴴ * W₁ᴴ = 1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp h₁
    have hu₂ : (W₂ᴴ)ᴴ * W₂ᴴ = 1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp h₂
    have hu₃ : (W₃ᴴ)ᴴ * W₃ᴴ = 1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp h₃
    have he := isQutritZeroFamilyMember_local_unitary W₁ᴴ W₂ᴴ W₃ᴴ hu₁ hu₂ hu₃ _ h
    simpa only [qutrit_unitary_embed_recover W₁ W₂ W₃ h₁ h₂ h₃ C] using he
  · exact isQutritZeroFamilyMember_local_unitary W₁ W₂ W₃ h₁ h₂ h₃ C

end ThreeCopyQutritWerner
