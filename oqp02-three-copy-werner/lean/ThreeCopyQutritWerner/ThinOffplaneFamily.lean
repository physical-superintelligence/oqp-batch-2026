module

public import ThreeCopyQutritWerner.ThinOffplaneDichotomy
public import ThreeCopyQutritWerner.ThinRankOnePencilSwap

@[expose] public section


/-! The complete actual nonzero off-plane-input branch of a thin zero. -/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem isQutritZeroFamilyMember_of_nonzero_offplane_factor
    (X Y : Matrix QutritSites (Fin 2) ℂ) (hX : X.rank = 2)
    (h2 : firstSiteFactorBlock X 2 = 0)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hN : frobSq (X * Yᴴ) = 1) (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0)
    (hne : firstSiteFactorBlock Y 2 ≠ 0) : IsQutritZeroFamilyMember (X * Yᴴ) := by
  rcases thinFirstSite_nonzero_offplane_source_dichotomy X Y hX hC hz hrow hne with
    hs | hf | hf
  · exact isQutritZeroFamilyMember_of_single_first_output (X * Yᴴ) hC hz hN hs
  · exact isQutritZeroFamilyMember_of_firstSite_rank_one_pencil X Y h2 hC hz hN hrow hf
  · exact isQutritZeroFamilyMember_of_firstSite_other_rank_one_pencil X Y h2 hC hz hN hrow hf

end ThreeCopyQutritWerner
