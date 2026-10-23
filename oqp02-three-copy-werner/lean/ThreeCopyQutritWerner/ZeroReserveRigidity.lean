module

public import ThreeCopyQutritWerner.ZeroReserveFamilyCoordinates
public import ThreeCopyQutritWerner.SharpFamilyThinCoordinates
public import ThreeCopyQutritWerner.ZeroReserveRankThreeReduction
public import ThreeCopyQutritWerner.ZeroReserveSmallRank

@[expose] public section


/-!
# Positive reserve rigidity and Appendix C input 1

The actual rank-three transition branch has a common thin physical factor.
Together with the smaller transition ranks this closes positive rank-two
reserve rigidity. The original scalar-square and balanced-source reduction
then supplies all of Appendix C input 1, without a classification
hypothesis.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- A rank-three saturated transition with positive cut entropies forces
thinness of its original weighted two-source operator. -/
theorem zeroReserve_rank_three_cut_thin
    (u v : QutritSites → ℂ) (z w : ℂ)
    (hu : 0 < vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u)))
    (hv : 0 < vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)))
    (heq : nuclearTrace (ptraceL (ketBra u v)) ^ 2 - frobSq (ptraceL (ketBra u v)) =
      Real.sqrt ((vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u))) *
        (vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)))))
    (hr : (ptraceL (ketBra u v)).rank = 3)
    (hsat : frobSq (ptraceL (ptraceL (ketBra u v))) +
        frobSq (ptraceR (ptraceL (ketBra u v))) =
      nuclearTrace (ptraceL (ketBra u v)) ^ 2 +
        Complex.normSq (ptraceL (ketBra u v)).trace) :
    HasThinLocalRange (z • ketBra u u + w • ketBra v v) := by
  obtain ⟨hRu, hRv⟩ := zeroReserve_cut_transition_equality_ranges u v hu hv heq
  have hf := sharpPartialTrace_rank_three_family_common_support
    (ptraceL (ketBra u v)) hr hsat
  rcases sharpQutritFamilyCommonSupport_exists_annihilator _ _ hf with
    ⟨U, a, hU, ha⟩ | ⟨U, a, hU, ha⟩
  · obtain ⟨hua, hva⟩ := zeroReserve_singular_first_annihilator_sources u v hRu hRv U a ha
    exact Or.inr (Or.inl (localRangeDim₂_two_ray_le_two_of_common_annihilator
      u v z w U hU a hua hva))
  · obtain ⟨hua, hva⟩ := zeroReserve_singular_second_annihilator_sources u v hRu hRv U a ha
    exact Or.inr (Or.inr (localRangeDim₃_two_ray_le_two_of_common_annihilator
      u v z w U hU a hua hva))

/-- Every actual positive rank-two qutrit reserve zero has a thin physical
local range. No endpoint inequality or supplied equality classification is used. -/
theorem zeroReserve_posSemidef_rank_two_thin
    (P : Matrix QutritSites QutritSites ℂ) (hP : P.PosSemidef)
    (hr : P.rank = 2) (hz : zeroReserve P = 0) : HasThinLocalRange P := by
  by_contra hn
  obtain ⟨u, v, lam, mu, hu, hv, huv, hlam, hmu, hdecomp, hpos⟩ :=
    zeroReserve_posSemidef_rank_two_non_thin_positive_entropies P hP hr hz hn
  have hz' : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0 := by
    rwa [← hdecomp]
  have hn' : ¬ HasThinLocalRange ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) := by
    rwa [← hdecomp]
  have ht := zeroReserve_two_ray_non_thin_first_transition_rank_three
    u v hu hv huv lam mu hlam hmu hz' hn'
  have hR (q : QutritSites → ℂ) :
      ptrace₂₃ (ketBra q q) = ptraceR (ketBra q q) := by
    ext i j
    simp only [ptrace₂₃, ptraceR, Fintype.sum_prod_type]
  have hL : ptrace₁ (ketBra u v) = ptraceL (ketBra u v) := rfl
  have huf : 0 < vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u)) := by
    simpa only [hu, one_pow, zeroReserveLocalDeficit, Matrix.cons_val_zero,
      hR] using (hpos 0).1
  have hvf : 0 < vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)) := by
    simpa only [hv, one_pow, zeroReserveLocalDeficit, Matrix.cons_val_zero,
      hR] using (hpos 0).2
  have he := ((zeroReserve_two_ray_eq_zero_saturates
    u v hu hv huv lam mu hlam hmu hz').1 0).2
  have heq : nuclearTrace (ptraceL (ketBra u v)) ^ 2 - frobSq (ptraceL (ketBra u v)) =
      Real.sqrt ((vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u))) *
        (vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)))) := by
    simpa only [zeroReserveCutNuclearDefect, zeroReserveLocalDeficit,
      Matrix.cons_val_zero, hu, hv, one_pow, hL, hR] using he
  have hs := zeroReserve_two_ray_eq_zero_transition_saturation
    u v hu hv huv lam mu hlam hmu hz' 0
  exact hn' (zeroReserve_rank_three_cut_thin u v (lam : ℂ) (mu : ℂ) huf hvf heq ht hs)

/-- All positive rank-at-most-two reserve zeros have a thin physical range. -/
theorem zeroReserve_posSemidef_rank_le_two_thin
    (P : Matrix QutritSites QutritSites ℂ) (hP : P.PosSemidef)
    (hr : P.rank ≤ 2) (hz : zeroReserve P = 0) : HasThinLocalRange P := by
  by_cases htwo : P.rank = 2
  · exact zeroReserve_posSemidef_rank_two_thin P hP htwo hz
  · exact Or.inl (zeroReserve_posSemidef_rank_le_one_thin P hP (by omega) hz)

/-- The full original Appendix C input 1, including its common range/corange
site assertion, follows without a remaining classification premise. -/
theorem appCInput1_proved : AppCInput1 :=
  appCInput1_of_positive_reserve_rigidity zeroReserve_posSemidef_rank_le_two_thin

end ThreeCopyQutritWerner
