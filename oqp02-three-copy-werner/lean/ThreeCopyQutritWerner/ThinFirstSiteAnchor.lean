module

public import ThreeCopyQutritWerner.ThinFirstSiteZeros
public import ThreeCopyQutritWerner.ThinScalarPlane
public import ThreeCopyQutritWerner.TwoCutQutritClassification
public import ThreeCopyQutritWerner.QutritThinFrame

@[expose] public section


/-!
# An actual two-site anchor or the unrestricted family-I branch

Five literal contractions suffice: two off-plane blocks, two off-diagonal
binary blocks, and one traceless binary ray contraction. If all vanish as
matrices, the original matrix is a plane projector tensor an arbitrary
nine-dimensional factor. Otherwise an actual nonzero rank-two cut zero is
available. Aligning its carrier across the remaining contractions is separate.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- A bounded list of actual contractions of the original matrix. -/
def thinFirstSiteAnchor (C : Matrix QutritSites QutritSites ℂ) (i : Fin 5) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  ![firstSiteBlock C 0 2, firstSiteBlock C 1 2,
    firstSiteBlock C 0 1, firstSiteBlock C 1 0,
    firstSiteContraction C ![1, 1, 0] ![1, -1, 0]] i

/-- The original thin zero supplies the rank and zero data for every anchor. -/
theorem thinFirstSiteAnchor_rank_cut_zero
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hrow : ∀ r q, C (2, r) q = 0) (i : Fin 5) :
    (thinFirstSiteAnchor C i).rank ≤ 2 ∧ cutForm (thinFirstSiteAnchor C i) = 0 := by
  obtain ⟨h01, h10, hreal, _⟩ := endpointEnergy_missing_first_row_two_six_zeros C hC hz hrow
  have hoff := firstSiteBlock_cutForm_zero_of_thin_endpoint_zero C hC hz 2 hrow
  fin_cases i
  · exact ⟨(firstSiteBlock_rank_le C 0 2).trans hC, hoff 0⟩
  · exact ⟨(firstSiteBlock_rank_le C 1 2).trans hC, hoff 1⟩
  · exact ⟨(firstSiteBlock_rank_le C 0 1).trans hC, h01⟩
  · exact ⟨(firstSiteBlock_rank_le C 1 0).trans hC, h10⟩
  · exact ⟨(firstSiteContraction_rank_le C _ _).trans hC, hreal⟩

/-- If the actual anchor matrices all vanish, the complete original matrix
has a scalar plane factor, with no restriction on its inactive factor. -/
theorem thinFirstSiteAnchor_all_zero_scalar_plane
    (C : Matrix QutritSites QutritSites ℂ)
    (hrow : ∀ r q, C (2, r) q = 0) (h : ∀ i, thinFirstSiteAnchor C i = 0) :
    C = (qutritPlaneInclusion 2 * (qutritPlaneInclusion 2)ᴴ) ⊗ₖ
      firstSiteBlock C 0 0 := by
  have h02 : firstSiteBlock C 0 2 = 0 := h 0
  have h12 : firstSiteBlock C 1 2 = 0 := h 1
  have h01 : firstSiteBlock C 0 1 = 0 := h 2
  have h10 : firstSiteBlock C 1 0 = 0 := h 3
  have hd : firstSiteBlock C 0 0 = firstSiteBlock C 1 1 := by
    have hh : firstSiteContraction C ![1, 1, 0] ![1, -1, 0] = 0 := h 4
    rw [(firstSiteContraction_pauli_coordinates C).1, h10, h01, sub_self, add_zero] at hh
    exact sub_eq_zero.mp hh
  have hb (j : Fin 3) : firstSiteBlock C 2 j = 0 := by
    ext r s
    exact hrow r (j, s)
  rw [qutritPlaneInclusion_projection]
  ext ⟨i, r⟩ ⟨j, s⟩
  change firstSiteBlock C i j r s =
    sharpCoordinatePlaneProjection 2 i j * firstSiteBlock C 0 0 r s
  fin_cases i <;> fin_cases j <;>
    simp [sharpCoordinatePlaneProjection, Matrix.diagonal_apply,
      h02, h12, h01, h10, hb, ← hd]

/-- The exact remaining alternative: either the original normalized matrix
is family I, or a selected original contraction is a nonzero rank-two cut
zero with its own constructed common binary carrier. No global alignment
of these independently constructed carriers is claimed. -/
theorem thinFirstSite_family_or_actual_binary_anchor
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hN : frobSq C = 1) (hz : endpointEnergy C = 0)
    (hrow : ∀ r q, C (2, r) q = 0) :
    IsQutritZeroFamilyMember C ∨
      ∃ i : Fin 5, (thinFirstSiteAnchor C i).rank = 2 ∧
        cutForm (thinFirstSiteAnchor C i) = 0 ∧
        ∃ J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ,
          ∃ K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
          J₁ᴴ * J₁ = 1 ∧ J₂ᴴ * J₂ = 1 ∧
            thinFirstSiteAnchor C i = (J₁ ⊗ₖ J₂) * K * (J₁ ⊗ₖ J₂)ᴴ := by
  by_cases ha : ∀ i, thinFirstSiteAnchor C i = 0
  · left
    exact isQutritZeroFamilyMember_of_scalar_plane_tensor C hC hN
      (qutritPlaneInclusion 2) (qutritPlaneInclusion_isometry 2)
      (firstSiteBlock C 0 0) (thinFirstSiteAnchor_all_zero_scalar_plane C hrow ha)
  · push_neg at ha
    obtain ⟨i, hi⟩ := ha
    obtain ⟨hr, hq⟩ := thinFirstSiteAnchor_rank_cut_zero C hC hz hrow i
    exact Or.inr ⟨i, rank_two_of_nonzero_cutForm_zero _ hr hq hi, hq,
      cutForm_zero_exists_binary_carrier _ hr hq⟩

end ThreeCopyQutritWerner
