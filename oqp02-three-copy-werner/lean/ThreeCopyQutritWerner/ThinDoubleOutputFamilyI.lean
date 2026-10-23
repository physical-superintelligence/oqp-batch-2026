module

public import ThreeCopyQutritWerner.ThinDoubleOutputProjection
public import ThreeCopyQutritWerner.ThinScalarPlane
public import ThreeCopyQutritWerner.QutritThinFrame
public import ThreeCopyQutritWerner.BinaryPartitionFamilyPlacement

@[expose] public section


/-!
# The original family-I branch with two fixed output coordinates

The shared orthogonal rank-two projector supplies an actual two-column
isometry. Moving its site to the first position gives the exact scalar-plane
tensor, which is normalized and restored to the original physical placement.
The inactive input vector is an unrestricted two-qutrit vector.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- A qutrit rank-two orthogonal projector is the projector of an actual
constructed two-column isometry, with no chosen frame in the hypotheses. -/
theorem qutrit_orthogonal_rank_two_projection_frame
    (P : Matrix (Fin 3) (Fin 3) ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) (hr : P.rank = 2) :
    ∃ J : Matrix (Fin 3) (Fin 2) ℂ, Jᴴ * J = 1 ∧ P = J * Jᴴ := by
  obtain ⟨J, hJ, hfix⟩ := qutrit_rank_le_two_exists_binary_frame P hr.le
  have hQ : (J * Jᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self J
  have hQQ : (J * Jᴴ) * (J * Jᴴ) = J * Jᴴ := by
    calc
      _ = J * (Jᴴ * J) * Jᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJ, Matrix.mul_one]
  have hQr : (J * Jᴴ).rank = 2 := by
    simpa only [Matrix.mul_one, Matrix.rank_one, Fintype.card_fin] using
      productRay_rank_conj_isometry J hJ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have hR : LinearMap.range P.mulVecLin ≤ LinearMap.range (J * Jᴴ).mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨P *ᵥ v, ?_⟩
    change (J * Jᴴ) *ᵥ (P *ᵥ v) = P *ᵥ v
    rw [Matrix.mulVec_mulVec, hfix]
  exact ⟨J, hJ, matrix_hermitian_idempotent_eq_of_range_le_rank_le
    P (J * Jᴴ) hP hQ hPP hQQ hR (by omega)⟩

/-- This branch is an actual original-coordinate member of the family union. The active projector is at site three; arbitrary inactive
input entanglement and complex phase survive the normalization. -/
theorem isQutritZeroFamilyMember_of_two_output_coordinates
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1) (k l : Fin 3)
    (hrow₁ : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0)
    (hrow₂ : ∀ j, j ≠ l → ∀ i r q, C (i, j, r) q = 0) :
    IsQutritZeroFamilyMember C := by
  have hne : C ≠ 0 := by
    intro he
    simp [he, frobSq] at hN
  obtain ⟨P, v, hP, hPP, hPr, he⟩ :=
    endpoint_zero_two_output_coordinates_projection C hC hz hne k l hrow₁ hrow₂
  obtain ⟨J, hJ, hPJ⟩ := qutrit_orthogonal_rank_two_projection_frame P hP hPP hPr
  let D := C.submatrix siteEquiv₃ siteEquiv₃
  let T : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
    fun p q => (if p.1 = k then 1 else 0) * (if p.2 = l then 1 else 0) * star (v q.1 q.2)
  have hD : D = (J * Jᴴ) ⊗ₖ T := by
    rw [← hPJ]
    ext p q
    change C (p.2.1, p.2.2, p.1) (q.2.1, q.2.2, q.1) = P p.1 q.1 * T p.2 q.2
    rw [he]
    simp only [T]
    ring
  have hDr : D.rank ≤ 2 := (Matrix.rank_submatrix C siteEquiv₃ siteEquiv₃).trans_le hC
  have hDN : frobSq D = 1 := (frobSq_submatrix_equiv siteEquiv₃ C).trans hN
  obtain ⟨χ, η, hχ, hη, hfamily⟩ :=
    qutrit_scalar_plane_normalized_familyI D hDr hDN J hJ T hD
  obtain ⟨h₀, h₁, h₀₁⟩ := binaryPartition_two_column_orthonormal J hJ
  apply binaryPartition_familyI_placement_member C 2 _ _ χ η h₀ h₁ h₀₁ hχ hη
  exact hfamily

end ThreeCopyQutritWerner
