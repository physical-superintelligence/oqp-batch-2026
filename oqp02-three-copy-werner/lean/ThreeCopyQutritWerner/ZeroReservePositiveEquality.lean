module

public import ThreeCopyQutritWerner.ZeroReserveDegenerate

@[expose] public section


/-!
# Actual positive rank-two sources in the reserve equality chain

Rank exactly two excludes a zero spectral weight. Thus the positive-weight
equality conditions apply to every actual positive rank-two reserve zero,
without requiring a supplied decomposition or positive eigenvalues.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

/-- A scaled rank-one operator factors through the literal one-column space. -/
theorem zeroReserve_rank_smul_ketBra_le_one {n : Type*} [Fintype n]
    (u v : n → ℂ) (z : ℂ) : (z • ketBra u v).rank ≤ 1 := by
  apply (rank_le_iff_exists_mul _ 1).mpr
  refine ⟨Matrix.of (fun i (_ : Fin 1) => z * u i),
    Matrix.of (fun (_ : Fin 1) j => conj (v j)), ?_⟩
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, ketBra]
  ring

/-- Exact positive rank two supplies two strictly positive spectral weights. -/
theorem posSemidef_rank_two_exists_positive_rays {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (hP : P.PosSemidef) (hr : P.rank = 2) :
    ∃ (u v : n → ℂ) (lam mu : ℝ),
      vecNormSq u = 1 ∧ vecNormSq v = 1 ∧ braket u v = 0 ∧
      0 < lam ∧ 0 < mu ∧ P = (lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v := by
  have hn : 2 ≤ Fintype.card n := hr.symm.trans_le (Matrix.rank_le_card_height P)
  obtain ⟨u, v, lam, mu, hu, hv, huv, hlam, hmu, hdecomp⟩ :=
    posSemidef_rank_le_two_exists_rays P hP hr.le hn
  have hlam_ne : lam ≠ 0 := by
    intro h
    have hsmall := zeroReserve_rank_smul_ketBra_le_one v v (mu : ℂ)
    rw [h] at hdecomp
    simp only [Complex.ofReal_zero, zero_smul, zero_add] at hdecomp
    rw [← hdecomp, hr] at hsmall
    omega
  have hmu_ne : mu ≠ 0 := by
    intro h
    have hsmall := zeroReserve_rank_smul_ketBra_le_one u u (lam : ℂ)
    rw [h] at hdecomp
    simp only [Complex.ofReal_zero, zero_smul, add_zero] at hdecomp
    rw [← hdecomp, hr] at hsmall
    omega
  exact ⟨u, v, lam, mu, hu, hv, huv, lt_of_le_of_ne hlam (Ne.symm hlam_ne),
    lt_of_le_of_ne hmu (Ne.symm hmu_ne), hdecomp⟩

/-- Every actual positive rank-two reserve zero has spectral rays with exact
weighted entropy balance and all cutwise sharp equalities. -/
theorem zeroReserve_posSemidef_rank_two_exists_saturated_rays
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (P : Matrix (a × b × c) (a × b × c) ℂ)
    (hP : P.PosSemidef) (hr : P.rank = 2) (hz : zeroReserve P = 0) :
    ∃ (u v : a × b × c → ℂ) (lam mu : ℝ),
      vecNormSq u = 1 ∧ vecNormSq v = 1 ∧ braket u v = 0 ∧
      0 < lam ∧ 0 < mu ∧ P = (lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v ∧
      (∀ i, lam * Real.sqrt (zeroReserveLocalDeficit u i) =
        mu * Real.sqrt (zeroReserveLocalDeficit v i)) ∧
      (∀ i, zeroReserveCutCross u v i = zeroReserveCutNuclearDefect u v i ∧
        zeroReserveCutNuclearDefect u v i =
          Real.sqrt (zeroReserveLocalDeficit u i * zeroReserveLocalDeficit v i)) := by
  obtain ⟨u, v, lam, mu, hu, hv, huv, hlam, hmu, hdecomp⟩ :=
    posSemidef_rank_two_exists_positive_rays P hP hr
  have hzero : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0 := by
    rw [← hdecomp]
    exact hz
  exact ⟨u, v, lam, mu, hu, hv, huv, hlam, hmu, hdecomp,
    zeroReserve_two_ray_eq_zero_local_balance u v hu hv huv lam mu hlam hmu hzero,
    (zeroReserve_two_ray_eq_zero_saturates u v hu hv huv lam mu hlam hmu hzero).1⟩

/-- If an actual positive rank-two reserve zero has no thin site, its actual
spectral rays have strictly positive entropy at every site. -/
theorem zeroReserve_posSemidef_rank_two_non_thin_positive_entropies
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (P : Matrix (a × b × c) (a × b × c) ℂ)
    (hP : P.PosSemidef) (hr : P.rank = 2) (hz : zeroReserve P = 0)
    (hn : ¬ HasThinLocalRange P) :
    ∃ (u v : a × b × c → ℂ) (lam mu : ℝ),
      vecNormSq u = 1 ∧ vecNormSq v = 1 ∧ braket u v = 0 ∧
      0 < lam ∧ 0 < mu ∧ P = (lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v ∧
      (∀ i, 0 < zeroReserveLocalDeficit u i ∧ 0 < zeroReserveLocalDeficit v i) := by
  obtain ⟨u, v, lam, mu, hu, hv, huv, hlam, hmu, hdecomp⟩ :=
    posSemidef_rank_two_exists_positive_rays P hP hr
  have hzero : zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = 0 := by
    rw [← hdecomp]
    exact hz
  have hne (i) : zeroReserveLocalDeficit u i ≠ 0 := by
    intro he
    apply hn
    rw [hdecomp]
    exact zeroReserve_two_ray_eq_zero_thin_of_deficit_zero
      u v hu hv huv lam mu hlam hmu hzero ⟨i, he⟩
  refine ⟨u, v, lam, mu, hu, hv, huv, hlam, hmu, hdecomp, ?_⟩
  intro i
  have hnv : zeroReserveLocalDeficit v i ≠ 0 := by
    intro he
    exact hne i ((zeroReserve_two_ray_eq_zero_deficit_zero_iff
      u v hu hv huv lam mu hlam hmu hzero i).mpr he)
  exact ⟨lt_of_le_of_ne (zeroReserveLocalDeficit_nonneg u hu i) (Ne.symm (hne i)),
    lt_of_le_of_ne (zeroReserveLocalDeficit_nonneg v hv i) (Ne.symm hnv)⟩

end ThreeCopyQutritWerner
