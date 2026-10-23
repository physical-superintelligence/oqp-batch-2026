module

public import ThreeCopyQutritWerner.ThinPencilLocalPlane
public import ThreeCopyQutritWerner.ThinRankOnePencilSwap

@[expose] public section


/-! Original corange-line exceptions and the two actual retained-site planes. -/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem isQutritZeroFamilyMember_of_partner_retained_line
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hN : frobSq (X * Yᴴ) = 1)
    (hline : (coherentFlatten₂ Y).rank ≤ 1 ∨ (coherentFlatten₃ Y).rank ≤ 1) :
    IsQutritZeroFamilyMember (X * Yᴴ) := by
  apply isQutritZeroFamilyMember_of_local_corange_line (X * Yᴴ) hC hz hN
  rcases hline with h | h
  · right
    left
    rw [localCorangeDim₂_eq_localRangeDim_adjoint, localRangeDim₂_eq_coherentFlatten_rank,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact (coherentFlatten₂_mul_rank_le Y Xᴴ).trans h
  · right
    right
    rw [localCorangeDim₃_eq_localRangeDim_adjoint, localRangeDim₃_eq_coherentFlatten_rank,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact (coherentFlatten₃_mul_rank_le Y Xᴴ).trans h

theorem thinFirstSite_member_or_retained_plane
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hX2 : firstSiteFactorBlock X 2 = 0) (hY2 : firstSiteFactorBlock Y 2 = 0)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hN : frobSq (X * Yᴴ) = 1)
    (hr : ∀ z w : ℂ, (twoSiteJointFactorFlatten
      (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1)
      (firstSiteFactorBlock Y 1 - w • firstSiteFactorBlock Y 0)).rank ≤ 2)
    (z₀ : ℂ) (hA : (twoSiteFactorFlatten
      (firstSiteFactorBlock X 0 + z₀ • firstSiteFactorBlock X 1)).rank = 2) :
    IsQutritZeroFamilyMember (X * Yᴴ) ∨
      ∃ P : Submodule ℂ (Fin 3 → ℂ), Module.finrank ℂ P = 2 ∧
        (∀ j, (coherentFlatten₂ X).col j ∈ P) ∧
        (∀ j, (coherentFlatten₂ Y).col j ∈ P) := by
  rcases thinFirstSite_local_plane_or_partner_line X Y hX2 hY2 hr z₀ hA with hp | hl
  · exact Or.inr hp
  · exact Or.inl (isQutritZeroFamilyMember_of_partner_retained_line X Y hC hz hN (Or.inl hl))

theorem thinFirstSite_member_or_other_retained_plane
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hX2 : firstSiteFactorBlock X 2 = 0) (hY2 : firstSiteFactorBlock Y 2 = 0)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hN : frobSq (X * Yᴴ) = 1)
    (hr : ∀ z w : ℂ, (twoSiteJointFactorFlatten
      (twoSiteFactorFlip (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1))
      (twoSiteFactorFlip (firstSiteFactorBlock Y 1 - w • firstSiteFactorBlock Y 0))).rank ≤ 2)
    (z₀ : ℂ) (hA : (twoSiteFactorFlatten (twoSiteFactorFlip
      (firstSiteFactorBlock X 0 + z₀ • firstSiteFactorBlock X 1))).rank = 2) :
    IsQutritZeroFamilyMember (X * Yᴴ) ∨
      ∃ P : Submodule ℂ (Fin 3 → ℂ), Module.finrank ℂ P = 2 ∧
        (∀ j, (coherentFlatten₃ X).col j ∈ P) ∧
        (∀ j, (coherentFlatten₃ Y).col j ∈ P) := by
  let X' := thinRemainingFactorSwap X
  let Y' := thinRemainingFactorSwap Y
  have hX2' : firstSiteFactorBlock X' 2 = 0 := by
    rw [show X' = thinRemainingFactorSwap X from rfl, firstSiteFactorBlock_remaining_swap, hX2]
    rfl
  have hY2' : firstSiteFactorBlock Y' 2 = 0 := by
    rw [show Y' = thinRemainingFactorSwap Y from rfl, firstSiteFactorBlock_remaining_swap, hY2]
    rfl
  rcases thinFirstSite_local_plane_or_partner_line X' Y' hX2' hY2'
      (fun z w => hr z w) z₀ hA with hp | hl
  · exact Or.inr hp
  · exact Or.inl (isQutritZeroFamilyMember_of_partner_retained_line X Y hC hz hN (Or.inr hl))

end ThreeCopyQutritWerner
