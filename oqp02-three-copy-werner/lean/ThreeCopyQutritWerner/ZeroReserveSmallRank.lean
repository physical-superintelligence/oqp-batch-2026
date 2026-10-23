module

public import ThreeCopyQutritWerner.PositiveRankOne
public import ThreeCopyQutritWerner.ZeroReservePureEquality
public import ThreeCopyQutritWerner.AppendixCScalarReduction

@[expose] public section


/-!
# The rank-zero and rank-one branches of positive reserve rigidity

Actual pure-source reserve is one quarter of total local linear entropy.
Its vanishing forces a pure first-site reduction and hence a thin source.
Only the rank-exactly-two rigidity theorem remains in the AppC-1 reduction.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- Every unit pure reserve zero has a pure first local marginal. -/
theorem zeroReserve_pure_zero_first_purity
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (u : a × b × c → ℂ) (hu : vecNormSq u = 1)
    (hz : zeroReserve (ketBra u u) = 0) :
    frobSq (ptrace₂₃ (ketBra u u)) = 1 := by
  have h := zeroReserve_pure u hu
  rw [hz, zeroReserveLocalEntropy_eq] at h
  obtain ⟨h1, h2, h3⟩ := zeroReserveLocalEntropy_deficits_nonneg u hu
  linarith

/-- A positive rank-at-most-one reserve zero has an actual thin first site. -/
theorem zeroReserve_posSemidef_rank_le_one_thin
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (P : Matrix (a × b × c) (a × b × c) ℂ)
    (hP : P.PosSemidef) (hr : P.rank ≤ 1) (hz : zeroReserve P = 0) :
    localRangeDim₁ P ≤ 2 := by
  by_cases h0 : P = 0
  · have ht : ptrace₂₃ (0 : Matrix (a × b × c) (a × b × c) ℂ) = 0 := by
      ext i j
      change (∑ _ : b, ∑ _ : c, (0 : ℂ)) = 0
      simp
    simp [h0, localRangeDim₁, ht]
  obtain ⟨u, lam, hu, hlam, hdecomp⟩ :=
    posSemidef_rank_le_one_exists_positive_ray P hP hr h0
  have hnorm : Complex.normSq (lam : ℂ) ≠ 0 := by
    rw [Complex.normSq_ofReal]
    exact mul_ne_zero (ne_of_gt hlam) (ne_of_gt hlam)
  have hpure : zeroReserve (ketBra u u) = 0 := by
    rw [hdecomp, zeroReserve_smul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hnorm
  have hpurity := zeroReserve_pure_zero_first_purity u hu hpure
  have hthin := zeroReserve_localRange1_le_two_of_local_purity_one u u hu hu
    hpurity hpurity (lam : ℂ) 0
  simpa only [zero_smul, add_zero, ← hdecomp] using hthin

/-- Rank-exactly-two reserve rigidity is now the sole positive-source
classification premise needed to obtain all of AppCInput1. -/
theorem appCInput1_of_rank_two_positive_reserve_rigidity
    (hrigidity : ∀ P : Matrix QutritSites QutritSites ℂ,
      P.PosSemidef → P.rank = 2 → zeroReserve P = 0 → HasThinLocalRange P) :
    AppCInput1 := by
  apply appCInput1_of_positive_reserve_rigidity
  intro P hP hr hz
  by_cases htwo : P.rank = 2
  · exact hrigidity P hP htwo hz
  · exact Or.inl (zeroReserve_posSemidef_rank_le_one_thin P hP (by omega) hz)

end ThreeCopyQutritWerner
