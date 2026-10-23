module

public import ThreeCopyQutritWerner.ThinFactorClassification
public import ThreeCopyQutritWerner.ThinPencilReduction

@[expose] public section


/-! Original normalized endpoint zeros with one actual missing output coordinate. -/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem isQutritZeroFamilyMember_of_missing_first_row_two
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1)
    (hrow : ∀ r q, C (2, r) q = 0) : IsQutritZeroFamilyMember C := by
  rcases thinFirstSite_family_or_full_factor_local_bounds C hC hz hN hrow with
    hm | ⟨X, Y, he, _, hX, _, hX2, hr⟩
  · exact hm
  rw [he] at hC hz hN hrow ⊢
  exact isQutritZeroFamilyMember_of_thin_factor_bounds X Y hX hX2 hC hz hN hrow hr

end ThreeCopyQutritWerner
