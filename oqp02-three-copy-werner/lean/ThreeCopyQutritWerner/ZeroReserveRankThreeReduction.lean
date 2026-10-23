module

public import ThreeCopyQutritWerner.ZeroReserveCommonKernelSupport
public import ThreeCopyQutritWerner.ZeroReservePositiveEquality
public import ThreeCopyQutritWerner.ZeroReserveSharpSaturation

@[expose] public section


/-!
# The remaining non-thin reserve-zero branch has transition rank three

The common-kernel support bound handles every first transition of rank at
most two directly. Since a first transition factors through its original
three-dimensional traced register, a non-thin source leaves precisely rank
three. This is a reduction, not a classification of that remaining branch.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- A first transition of rank at most two already bounds the actual source
at the first site. The entropy-zero case needs no transition rank assumption. -/
theorem zeroReserve_two_ray_first_transition_small_thin
    (u v : QutritSites → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hz : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0)
    (hr : (ptrace₁ (ketBra u v)).rank ≤ 2) :
    localRangeDim₁ ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) ≤ 2 := by
  by_cases hdu : zeroReserveLocalDeficit u 0 = 0
  · exact zeroReserve_two_ray_eq_zero_thin_site1 u v hu hv huv lam mu hlam hmu hz hdu
  · have hdv : zeroReserveLocalDeficit v 0 ≠ 0 := by
      intro h
      exact hdu ((zeroReserve_two_ray_eq_zero_deficit_zero_iff
        u v hu hv huv lam mu hlam hmu hz 0).mpr h)
    have hupos : 0 < zeroReserveLocalDeficit u 0 :=
      lt_of_le_of_ne (zeroReserveLocalDeficit_nonneg u hu 0) (Ne.symm hdu)
    have hvpos : 0 < zeroReserveLocalDeficit v 0 :=
      lt_of_le_of_ne (zeroReserveLocalDeficit_nonneg v hv 0) (Ne.symm hdv)
    have hR (q : QutritSites → ℂ) :
        ptraceR (ketBra q q) = ptrace₂₃ (ketBra q q) := by
      ext i j
      simp only [ptraceR, ptrace₂₃, Fintype.sum_prod_type]
    have hL : ptraceL (ketBra u v) = ptrace₁ (ketBra u v) := rfl
    have huf : 0 < vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u)) := by
      rw [hR u]
      simpa only [hu, one_pow, zeroReserveLocalDeficit, Matrix.cons_val_zero] using hupos
    have hvf : 0 < vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)) := by
      rw [hR v]
      simpa only [hv, one_pow, zeroReserveLocalDeficit, Matrix.cons_val_zero] using hvpos
    have he := ((zeroReserve_two_ray_eq_zero_saturates
      u v hu hv huv lam mu hlam hmu hz).1 0).2
    have heq : nuclearTrace (ptraceL (ketBra u v)) ^ 2 - frobSq (ptraceL (ketBra u v)) =
        Real.sqrt ((vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u))) *
          (vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)))) := by
      rw [hL, hR u, hR v]
      simpa only [zeroReserveCutNuclearDefect, zeroReserveLocalDeficit,
        Matrix.cons_val_zero, hu, hv, one_pow] using he
    exact (zeroReserve_localRange1_le_transition_rank u v
      (lam : ℂ) (mu : ℂ) huf hvf heq).trans hr

/-- Every non-thin positive-weight reserve zero has actual first transition
rank exactly three; no larger singular family needs consideration. -/
theorem zeroReserve_two_ray_non_thin_first_transition_rank_three
    (u v : QutritSites → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hz : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0)
    (hn : ¬ HasThinLocalRange ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v)) :
    (ptrace₁ (ketBra u v)).rank = 3 := by
  have hle : (ptrace₁ (ketBra u v)).rank ≤ 3 := by
    change (ptraceL (ketBra u v)).rank ≤ 3
    rw [zeroReserveCutFlatten_transition]
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin 3))
  have hnot : ¬ (ptrace₁ (ketBra u v)).rank ≤ 2 := by
    intro hr
    exact hn (Or.inl (zeroReserve_two_ray_first_transition_small_thin
      u v hu hv huv lam mu hlam hmu hz hr))
  omega

/-- REDUCTION: an actual positive rank-two reserve-zero source which is not
thin supplies a literal rank-three sharp transition and its original rays. -/
theorem zeroReserve_posSemidef_non_thin_exists_rank_three_transition
    (P : Matrix QutritSites QutritSites ℂ) (hP : P.PosSemidef)
    (hr : P.rank = 2) (hz : zeroReserve P = 0) (hn : ¬ HasThinLocalRange P) :
    ∃ (u v : QutritSites → ℂ) (lam mu : ℝ),
      vecNormSq u = 1 ∧ vecNormSq v = 1 ∧ braket u v = 0 ∧
      0 < lam ∧ 0 < mu ∧ P = (lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v ∧
      (ptrace₁ (ketBra u v)).rank = 3 ∧
      frobSq (ptraceL (ptrace₁ (ketBra u v))) +
        frobSq (ptraceR (ptrace₁ (ketBra u v))) =
      nuclearTrace (ptrace₁ (ketBra u v)) ^ 2 +
        Complex.normSq (ptrace₁ (ketBra u v)).trace := by
  obtain ⟨u, v, lam, mu, hu, hv, huv, hlam, hmu, hdecomp⟩ :=
    posSemidef_rank_two_exists_positive_rays P hP hr
  have hz' : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0 := by
    rwa [← hdecomp]
  have hn' : ¬ HasThinLocalRange ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) := by
    rwa [← hdecomp]
  exact ⟨u, v, lam, mu, hu, hv, huv, hlam, hmu, hdecomp,
    zeroReserve_two_ray_non_thin_first_transition_rank_three
      u v hu hv huv lam mu hlam hmu hz' hn',
    zeroReserve_two_ray_eq_zero_transition_saturation u v hu hv huv lam mu hlam hmu hz' 0⟩

end ThreeCopyQutritWerner
