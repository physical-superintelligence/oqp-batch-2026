module

public import ThreeCopyQutritWerner.ThinRankOnePencilFamily
public import ThreeCopyQutritWerner.TwoSiteJointFactorFlip

@[expose] public section


/-! The second retained-site rank-one pencil in the original operator. -/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

def thinRemainingFactorSwap (X : Matrix QutritSites (Fin 2) ℂ) :
    Matrix QutritSites (Fin 2) ℂ := X.submatrix qutritRemainingSwap id

theorem thinRemainingFactorSwap_product (X Y : Matrix QutritSites (Fin 2) ℂ) :
    thinRemainingFactorSwap X * (thinRemainingFactorSwap Y)ᴴ =
      (X * Yᴴ).submatrix qutritRemainingSwap qutritRemainingSwap := by
  unfold thinRemainingFactorSwap
  rw [Matrix.conjTranspose_submatrix]
  exact Matrix.submatrix_mul_equiv X Yᴴ qutritRemainingSwap
    (Equiv.refl (Fin 2)) qutritRemainingSwap

theorem firstSiteFactorBlock_remaining_swap (X : Matrix QutritSites (Fin 2) ℂ) (i : Fin 3) :
    firstSiteFactorBlock (thinRemainingFactorSwap X) i =
      twoSiteFactorFlip (firstSiteFactorBlock X i) := rfl

theorem endpointEnergy_remaining_swap (C : Matrix QutritSites QutritSites ℂ) :
    endpointEnergy (C.submatrix qutritRemainingSwap qutritRemainingSwap) = endpointEnergy C := by
  have he : C.submatrix qutritRemainingSwap qutritRemainingSwap =
      (C.submatrix siteEquiv₃ siteEquiv₃).submatrix siteEquiv₂ siteEquiv₂ := rfl
  rw [he]
  exact (energy_submatrix_siteEquiv₂ (1 / 2) (C.submatrix siteEquiv₃ siteEquiv₃)).trans
    (energy_submatrix_siteEquiv₃ (1 / 2) C)

theorem isQutritZeroFamilyMember_remaining_swap_iff
    (C : Matrix QutritSites QutritSites ℂ) :
    IsQutritZeroFamilyMember (C.submatrix qutritRemainingSwap qutritRemainingSwap) ↔
      IsQutritZeroFamilyMember C := by
  have he : C.submatrix qutritRemainingSwap qutritRemainingSwap =
      (C.submatrix siteEquiv₃ siteEquiv₃).submatrix siteEquiv₂ siteEquiv₂ := rfl
  rw [he]
  exact (isQutritZeroFamilyMember_site_iff (C.submatrix siteEquiv₃ siteEquiv₃) 1).trans
    (isQutritZeroFamilyMember_site_iff C 2)

theorem isQutritZeroFamilyMember_of_firstSite_other_rank_one_pencil
    (X Y : Matrix QutritSites (Fin 2) ℂ) (h2 : firstSiteFactorBlock X 2 = 0)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hN : frobSq (X * Yᴴ) = 1) (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0)
    (hr : ∀ z : ℂ, (twoSiteFactorFlatten (twoSiteFactorFlip
      (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1))).rank ≤ 1) :
    IsQutritZeroFamilyMember (X * Yᴴ) := by
  let X' := thinRemainingFactorSwap X
  let Y' := thinRemainingFactorSwap Y
  have he := thinRemainingFactorSwap_product X Y
  have h2' : firstSiteFactorBlock X' 2 = 0 := by
    rw [show X' = thinRemainingFactorSwap X from rfl, firstSiteFactorBlock_remaining_swap, h2]
    rfl
  have hC' : (X' * Y'ᴴ).rank ≤ 2 := by
    rw [show X' * Y'ᴴ = (X * Yᴴ).submatrix qutritRemainingSwap qutritRemainingSwap from he]
    exact (Matrix.rank_submatrix _ _ _).trans_le hC
  have hz' : endpointEnergy (X' * Y'ᴴ) = 0 := by
    rw [show X' * Y'ᴴ = (X * Yᴴ).submatrix qutritRemainingSwap qutritRemainingSwap from he,
      endpointEnergy_remaining_swap, hz]
  have hN' : frobSq (X' * Y'ᴴ) = 1 := by
    rw [show X' * Y'ᴴ = (X * Yᴴ).submatrix qutritRemainingSwap qutritRemainingSwap from he]
    exact (frobSq_submatrix_equiv qutritRemainingSwap (X * Yᴴ)).trans hN
  have hrow' : ∀ r q, (X' * Y'ᴴ) (2, r) q = 0 := by
    intro r q
    rw [show X' * Y'ᴴ = (X * Yᴴ).submatrix qutritRemainingSwap qutritRemainingSwap from he]
    exact hrow (r.2, r.1) (qutritRemainingSwap q)
  have hr' (z : ℂ) : (twoSiteFactorFlatten
      (firstSiteFactorBlock X' 0 + z • firstSiteFactorBlock X' 1)).rank ≤ 1 := by
    exact hr z
  have hm := isQutritZeroFamilyMember_of_firstSite_rank_one_pencil X' Y' h2' hC' hz' hN' hrow' hr'
  rw [show X' * Y'ᴴ = (X * Yᴴ).submatrix qutritRemainingSwap qutritRemainingSwap from he] at hm
  exact (isQutritZeroFamilyMember_remaining_swap_iff (X * Yᴴ)).mp hm

end ThreeCopyQutritWerner
