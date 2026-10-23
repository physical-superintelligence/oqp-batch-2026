module

public import ThreeCopyQutritWerner.ThinDoubleOutputFamilyI

@[expose] public section


/-! The other original placement of the two-fixed-output family-I branch. -/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem isQutritZeroFamilyMember_of_first_third_output_coordinates
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1) (k l : Fin 3)
    (hrow₁ : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0)
    (hrow₃ : ∀ r, r ≠ l → ∀ i j q, C (i, j, r) q = 0) :
    IsQutritZeroFamilyMember C := by
  let D := C.submatrix siteEquiv₃ siteEquiv₃
  have hDr : D.rank ≤ 2 := (Matrix.rank_submatrix C siteEquiv₃ siteEquiv₃).trans_le hC
  have hDz : endpointEnergy D = 0 := (energy_submatrix_siteEquiv₃ (1 / 2) C).trans hz
  have hDN : frobSq D = 1 := (frobSq_submatrix_equiv siteEquiv₃ C).trans hN
  have hDne : D ≠ 0 := by
    intro he
    simp [he, frobSq] at hDN
  have hDrow₁ : ∀ i, i ≠ l → ∀ r q, D (i, r) q = 0 := by
    intro i hi r q
    exact hrow₃ i hi r.1 r.2 (q.2.1, q.2.2, q.1)
  have hDrow₂ : ∀ j, j ≠ k → ∀ i r q, D (i, j, r) q = 0 := by
    intro j hj i r q
    exact hrow₁ j hj (r, i) (q.2.1, q.2.2, q.1)
  obtain ⟨P, v, hP, hPP, hPr, he⟩ :=
    endpoint_zero_two_output_coordinates_projection D hDr hDz hDne l k hDrow₁ hDrow₂
  obtain ⟨J, hJ, hPJ⟩ := qutrit_orthogonal_rank_two_projection_frame P hP hPP hPr
  let F := C.submatrix siteEquiv₂ siteEquiv₂
  let T : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
    fun p q => (if p.2 = l then 1 else 0) * (if p.1 = k then 1 else 0) * star (v q.2 q.1)
  have hF : F = (J * Jᴴ) ⊗ₖ T := by
    rw [← hPJ]
    ext p q
    have h := he (p.2.2, p.2.1, p.1) (q.2.2, q.2.1, q.1)
    change C (p.2.1, p.1, p.2.2) (q.2.1, q.1, q.2.2) =
      P p.1 q.1 * T p.2 q.2
    change C (p.2.1, p.1, p.2.2) (q.2.1, q.1, q.2.2) =
      (if p.2.2 = l then 1 else 0) * (if p.2.1 = k then 1 else 0) *
        star (v q.2.2 q.2.1) * P p.1 q.1 at h
    rw [h]
    simp only [T]
    ring
  have hFr : F.rank ≤ 2 := (Matrix.rank_submatrix C siteEquiv₂ siteEquiv₂).trans_le hC
  have hFN : frobSq F = 1 := (frobSq_submatrix_equiv siteEquiv₂ C).trans hN
  obtain ⟨χ, η, hχ, hη, hfamily⟩ :=
    qutrit_scalar_plane_normalized_familyI F hFr hFN J hJ T hF
  obtain ⟨h₀, h₁, h₀₁⟩ := binaryPartition_two_column_orthonormal J hJ
  apply binaryPartition_familyI_placement_member C 1 _ _ χ η h₀ h₁ h₀₁ hχ hη
  exact hfamily

end ThreeCopyQutritWerner
