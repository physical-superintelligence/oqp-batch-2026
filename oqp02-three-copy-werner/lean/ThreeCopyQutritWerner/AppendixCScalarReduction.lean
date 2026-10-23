module

public import ThreeCopyQutritWerner.CoherentShadowEquality
public import ThreeCopyQutritWerner.CoherentGramSupport
public import ThreeCopyQutritWerner.CoherentUnitCircle

@[expose] public section


/-!
# Exact remaining positive-source rigidity obligation for Appendix C input 1

The quantitative half is proved from the original hypotheses. The common-site
half is reduced to the explicit unresolved classification of positive reserve
zeros. This file does not assert that classification or an unconditional AppCInput1.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- If each actual positive source on the unit circle is thin somewhere, the
same original factors have a common thin range/corange site. -/
theorem common_local_support_of_unit_phase_thin_sources
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hthin : ∀ z : ℂ, Complex.normSq z = 1 →
      HasThinLocalRange (coherentPositiveSource X Y z)) :
    (localRangeDim₁ (X * Yᴴ) ≤ 2 ∧ localCorangeDim₁ (X * Yᴴ) ≤ 2) ∨
      (localRangeDim₂ (X * Yᴴ) ≤ 2 ∧ localCorangeDim₂ (X * Yᴴ) ≤ 2) ∨
        (localRangeDim₃ (X * Yᴴ) ≤ 2 ∧ localCorangeDim₃ (X * Yᴴ) ≤ 2) := by
  apply common_local_support_of_infinite_pencil_minors X Y
    {z : ℂ | Complex.normSq z = 1} coherentUnitPhases_infinite
  intro z hz
  exact coherentQutritFlatten_minors_of_thin_gram (X + z • Y) (hthin z hz)

/-- Precise reduction of AppC-1 to the remaining actual positive-source
reserve rigidity theorem; this hypothesis is explicitly unresolved. -/
theorem appCInput1_of_positive_reserve_rigidity
    (hrigidity : ∀ P : Matrix QutritSites QutritSites ℂ,
      P.PosSemidef → P.rank ≤ 2 → zeroReserve P = 0 → HasThinLocalRange P) :
    AppCInput1 := by
  intro C κ hr hκ
  refine ⟨singularGapSq_le_six_endpoint_of_scalar_square C hr κ hκ, ?_⟩
  intro hq
  obtain ⟨X, Y, hC, hG, hXY, hphase⟩ :=
    exists_balanced_coherent_zero_factors C hr κ hκ hq
  rw [hC]
  apply common_local_support_of_unit_phase_thin_sources X Y
  intro z hz
  exact hrigidity (coherentPositiveSource X Y z)
    (coherentPositiveSource_posSemidef X Y z)
    (by simpa using coherentPositiveSource_rank_le X Y z) (hphase z hz)

end ThreeCopyQutritWerner
