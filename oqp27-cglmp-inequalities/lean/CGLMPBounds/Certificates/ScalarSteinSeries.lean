module

public import CGLMPBounds.Certificates.ScalarSteinDerivatives

@[expose] public section


/-!
# Exact endpoint sums in the beta–Stein derivative estimates

The regularized cosecant series is differentiated on `(0,3/2)`, an open
neighborhood of one. A geometric majorant with ratio `9/16` justifies every
derivative. Explicit differentiation then evaluates the three endpoint sums
needed for the two sharp constants printed after (I.5).

No coefficient sum or analytic derivative
identity is assumed as a hypothesis.
-/

namespace CGLMPBounds.Certificates

open Filter Set
open scoped Topology

noncomputable section

def scalarRegularDerivativeTerm (i m : ℕ) (y : ℝ) : ℝ :=
  scalarCosecantCoefficient (i + 1) * scalarPowerDerivative (2 * i + 1) m y

def scalarRegularDerivativeSeries (m : ℕ) (y : ℝ) : ℝ := ∑' i, scalarRegularDerivativeTerm i m y

def scalarRegularDerivativeMajorant (m i : ℕ) : ℝ :=
  (4 / 3 : ℝ) * 2 ^ m * ((i : ℝ) + 1) ^ m * (9 / 16 : ℝ) ^ (i + 1)

theorem scalarRegularDerivativeTerm_bound (i m : ℕ) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) (3 / 2)) :
    ‖scalarRegularDerivativeTerm i m y‖ ≤ scalarRegularDerivativeMajorant m i := by
  have hy0 : 0 ≤ y := hy.1
  have hc := scalarCosecantCoefficient_pos_lt (i + 1) (by omega)
  have hpow : y ^ (2 * i + 1 - m) ≤ (3 / 2 : ℝ) ^ (2 * (i + 1)) :=
    (pow_le_pow_left₀ hy.1 hy.2 (2 * i + 1 - m)).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have hfac : ((2 * i + 1).descFactorial m : ℝ) ≤
      (2 * ((i : ℝ) + 1)) ^ m := by
    calc
      _ ≤ ((2 * i + 1 : ℕ) : ℝ) ^ m := by
        exact_mod_cast Nat.descFactorial_le_pow (2 * i + 1) m
      _ ≤ (2 * ((i : ℝ) + 1)) ^ m := by
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        linarith
  have hder : |scalarPowerDerivative (2 * i + 1) m y| ≤
      (2 * ((i : ℝ) + 1)) ^ m * (3 / 2 : ℝ) ^ (2 * (i + 1)) := by
    rw [scalarPowerDerivative, abs_of_nonneg (by positivity)]
    exact mul_le_mul hfac hpow (by positivity) (by positivity)
  have hgeom : (1 / 4 : ℝ) ^ (i + 1) * (3 / 2 : ℝ) ^ (2 * (i + 1)) =
      (9 / 16 : ℝ) ^ (i + 1) := by
    rw [pow_mul, ← mul_pow]
    norm_num
  rw [scalarRegularDerivativeTerm, Real.norm_eq_abs, abs_mul, abs_of_pos hc.1]
  calc
    _ ≤ ((4 / 3 : ℝ) * (1 / 4 : ℝ) ^ (i + 1)) *
        ((2 * ((i : ℝ) + 1)) ^ m * (3 / 2 : ℝ) ^ (2 * (i + 1))) :=
      mul_le_mul hc.2.le hder (abs_nonneg _) (by positivity)
    _ = scalarRegularDerivativeMajorant m i := by
      rw [scalarRegularDerivativeMajorant, mul_pow]
      calc
        _ = (4 / 3 : ℝ) * 2 ^ m * ((i : ℝ) + 1) ^ m *
            ((1 / 4 : ℝ) ^ (i + 1) * (3 / 2 : ℝ) ^ (2 * (i + 1))) := by ring
        _ = _ := by rw [hgeom]

theorem scalarRegularDerivativeMajorant_summable (m : ℕ) :
    Summable (scalarRegularDerivativeMajorant m) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one m
    (by norm_num : ‖(9 / 16 : ℝ)‖ < 1)
  have hs := (summable_nat_add_iff 1).2 h
  change Summable (fun i : ℕ =>
    (4 / 3 : ℝ) * 2 ^ m * ((i : ℝ) + 1) ^ m * (9 / 16 : ℝ) ^ (i + 1))
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using
    hs.mul_left ((4 / 3 : ℝ) * 2 ^ m)

theorem scalarRegularDerivativeTerm_summable (m : ℕ) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) (3 / 2)) : Summable (fun i => scalarRegularDerivativeTerm i m y) :=
  (scalarRegularDerivativeMajorant_summable m).of_norm_bounded
    (fun i => scalarRegularDerivativeTerm_bound i m hy)

theorem scalarRegularDerivativeSeries_hasDerivAt (m : ℕ) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) (3 / 2)) :
    HasDerivAt (scalarRegularDerivativeSeries m) (scalarRegularDerivativeSeries (m + 1) y) y := by
  apply hasDerivAt_tsum_of_isPreconnected (scalarRegularDerivativeMajorant_summable (m + 1))
    isOpen_Ioo (convex_Ioo (0 : ℝ) (3 / 2)).isPreconnected
    (fun i t _ => (scalarPowerDerivative_hasDerivAt (2 * i + 1) m t).const_mul _)
    (fun i t ht => scalarRegularDerivativeTerm_bound i (m + 1) ⟨ht.1.le, ht.2.le⟩)
    (show (1 : ℝ) ∈ Ioo (0 : ℝ) (3 / 2) by norm_num)
    (scalarRegularDerivativeTerm_summable m (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) (3 / 2))) hy

def scalarRegularAnalytic (y : ℝ) : ℝ :=
  1 / Real.sin ((Real.pi / 2) * y) - 1 / ((Real.pi / 2) * y)

def scalarRegularAnalyticFirst (y : ℝ) : ℝ :=
  -(Real.pi / 2) * Real.cos ((Real.pi / 2) * y) /
      Real.sin ((Real.pi / 2) * y) ^ 2 + 1 / ((Real.pi / 2) * y ^ 2)

def scalarRegularAnalyticSecond (y : ℝ) : ℝ :=
  (Real.pi / 2) ^ 2 / Real.sin ((Real.pi / 2) * y) +
    2 * (Real.pi / 2) ^ 2 * Real.cos ((Real.pi / 2) * y) ^ 2 /
      Real.sin ((Real.pi / 2) * y) ^ 3 - 2 / ((Real.pi / 2) * y ^ 3)

private theorem scalar_regular_sin_ne_zero {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) (3 / 2)) : Real.sin ((Real.pi / 2) * y) ≠ 0 := by
  apply (Real.sin_pos_of_pos_of_lt_pi _ _).ne'
  · exact mul_pos (by positivity : 0 < Real.pi / 2) hy.1
  · calc
      (Real.pi / 2) * y < (Real.pi / 2) * (3 / 2) :=
        mul_lt_mul_of_pos_left hy.2 (by positivity)
      _ < Real.pi := by nlinarith [Real.pi_pos]

theorem scalarRegularDerivativeSeries_zero_order {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) (3 / 2)) :
    scalarRegularDerivativeSeries 0 y = scalarRegularAnalytic y := by
  have h := scalar_cosecant_hasSum
    (show y ∈ Ioo (0 : ℝ) 2 from ⟨hy.1, by linarith [hy.2]⟩)
  simp only [scalarRegularDerivativeSeries, scalarRegularDerivativeTerm, scalarPowerDerivative,
    Nat.descFactorial_zero, Nat.cast_one, one_mul, Nat.sub_zero]
  rw [h.tsum_eq, scalarRegularAnalytic]
  have hy0 : y ≠ 0 := hy.1.ne'
  rw [show Real.pi * y / 2 = (Real.pi / 2) * y by ring]
  congr 1
  field_simp [Real.pi_ne_zero, hy0]
  <;> ring

theorem scalarRegularAnalytic_hasDerivAt {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) (3 / 2)) :
    HasDerivAt scalarRegularAnalytic (scalarRegularAnalyticFirst y) y := by
  have ha : Real.pi / 2 ≠ 0 := by positivity
  have hy0 : y ≠ 0 := hy.1.ne'
  have hs := scalar_regular_sin_ne_zero hy
  have hl := (hasDerivAt_id y).const_mul (Real.pi / 2)
  have hsin := (Real.hasDerivAt_sin ((Real.pi / 2) * y)).comp y hl
  have h := ((hasDerivAt_const y (1 : ℝ)).div hsin hs).sub
    ((hasDerivAt_const y (1 : ℝ)).div hl (mul_ne_zero ha hy0))
  convert h using 1
  · rfl
  · dsimp [scalarRegularAnalyticFirst]
    field_simp [hs, ha, hy0, Real.pi_ne_zero]
    <;> ring

theorem scalarRegularAnalyticFirst_hasDerivAt {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) (3 / 2)) :
    HasDerivAt scalarRegularAnalyticFirst (scalarRegularAnalyticSecond y) y := by
  have ha : Real.pi / 2 ≠ 0 := by positivity
  have hy0 : y ≠ 0 := hy.1.ne'
  have hs := scalar_regular_sin_ne_zero hy
  have hl := (hasDerivAt_id y).const_mul (Real.pi / 2)
  have hsin := (Real.hasDerivAt_sin ((Real.pi / 2) * y)).comp y hl
  have hcos := (Real.hasDerivAt_cos ((Real.pi / 2) * y)).comp y hl
  have h := ((hcos.const_mul (-(Real.pi / 2))).div (hsin.pow 2) (pow_ne_zero 2 hs)).add
    ((hasDerivAt_const y (1 : ℝ)).div
      (((hasDerivAt_id y).pow 2).const_mul (Real.pi / 2))
      (mul_ne_zero ha (pow_ne_zero 2 hy0)))
  convert h using 1
  · rfl
  · dsimp [scalarRegularAnalyticSecond]
    field_simp [hs, ha, hy0, Real.pi_ne_zero]
    <;> ring

theorem scalarRegularAnalyticSecond_hasDerivAt_one :
    HasDerivAt scalarRegularAnalyticSecond (12 / Real.pi) 1 := by
  have ha : Real.pi / 2 ≠ 0 := by positivity
  have hl : HasDerivAt (fun t : ℝ => (Real.pi / 2) * t) (Real.pi / 2) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).const_mul (Real.pi / 2)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin ((Real.pi / 2) * t)) 0 1 := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sin ((Real.pi / 2) * (1 : ℝ))).comp 1 hl
  have hcos : HasDerivAt (fun t : ℝ => Real.cos ((Real.pi / 2) * t)) (-(Real.pi / 2)) 1 := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_cos ((Real.pi / 2) * (1 : ℝ))).comp 1 hl
  have hs : Real.sin ((Real.pi / 2) * (1 : ℝ)) ≠ 0 := by simp
  have hfirst := (hasDerivAt_const (1 : ℝ) ((Real.pi / 2) ^ 2)).div hsin hs
  have hmiddle := ((hcos.pow 2).const_mul (2 * (Real.pi / 2) ^ 2)).div
    (hsin.pow 3) (pow_ne_zero 3 hs)
  have hpole := (hasDerivAt_const (1 : ℝ) (2 : ℝ)).div
    (((hasDerivAt_id (1 : ℝ)).pow 3).const_mul (Real.pi / 2)) (by simpa using ha)
  have h := (hfirst.add hmiddle).sub hpole
  convert h using 1
  · rfl
  · simp <;> field_simp [Real.pi_ne_zero]
    <;> ring

theorem scalarRegularDerivativeSeries_first_order {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) (3 / 2)) :
    scalarRegularDerivativeSeries 1 y = scalarRegularAnalyticFirst y := by
  have he : scalarRegularDerivativeSeries 0 =ᶠ[𝓝 y] scalarRegularAnalytic := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact scalarRegularDerivativeSeries_zero_order ht
  exact (scalarRegularDerivativeSeries_hasDerivAt 0 hy).unique
    ((scalarRegularAnalytic_hasDerivAt hy).congr_of_eventuallyEq he)

theorem scalarRegularDerivativeSeries_second_order {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) (3 / 2)) :
    scalarRegularDerivativeSeries 2 y = scalarRegularAnalyticSecond y := by
  have he : scalarRegularDerivativeSeries 1 =ᶠ[𝓝 y] scalarRegularAnalyticFirst := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact scalarRegularDerivativeSeries_first_order ht
  exact (scalarRegularDerivativeSeries_hasDerivAt 1 hy).unique
    ((scalarRegularAnalyticFirst_hasDerivAt hy).congr_of_eventuallyEq he)

theorem scalarRegularDerivativeSeries_first_one : scalarRegularDerivativeSeries 1 1 = 2 / Real.pi := by
  rw [scalarRegularDerivativeSeries_first_order (by norm_num), scalarRegularAnalyticFirst]
  simp <;> field_simp [Real.pi_ne_zero] <;> ring

theorem scalarRegularDerivativeSeries_second_one :
    scalarRegularDerivativeSeries 2 1 = Real.pi ^ 2 / 4 - 4 / Real.pi := by
  rw [scalarRegularDerivativeSeries_second_order (by norm_num), scalarRegularAnalyticSecond]
  simp <;> field_simp [Real.pi_ne_zero]
  <;> ring

theorem scalarRegularDerivativeSeries_third_one : scalarRegularDerivativeSeries 3 1 = 12 / Real.pi := by
  have he : scalarRegularDerivativeSeries 2 =ᶠ[𝓝 (1 : ℝ)] scalarRegularAnalyticSecond := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (by norm_num : (1 : ℝ) ∈ Ioo (0 : ℝ) (3 / 2))] with t ht
    exact scalarRegularDerivativeSeries_second_order ht
  exact (scalarRegularDerivativeSeries_hasDerivAt 2 (by norm_num)).unique
    (scalarRegularAnalyticSecond_hasDerivAt_one.congr_of_eventuallyEq he)

theorem scalarRegularDerivativeSeries_second_add_twice_first :
    scalarRegularDerivativeSeries 2 1 + 2 * scalarRegularDerivativeSeries 1 1 = Real.pi ^ 2 / 4 := by
  rw [scalarRegularDerivativeSeries_second_one, scalarRegularDerivativeSeries_first_one]
  ring

theorem scalarRegularDerivativeSeries_third_add_three_second :
    scalarRegularDerivativeSeries 3 1 + 3 * scalarRegularDerivativeSeries 2 1 = 3 * Real.pi ^ 2 / 4 := by
  rw [scalarRegularDerivativeSeries_third_one, scalarRegularDerivativeSeries_second_one]
  ring

theorem scalarRegularAnalytic_iteratedDeriv (m : ℕ) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) (3 / 2)) :
    iteratedDeriv m scalarRegularAnalytic y = scalarRegularDerivativeSeries m y := by
  induction m generalizing y with
  | zero => simpa using (scalarRegularDerivativeSeries_zero_order hy).symm
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv m scalarRegularAnalytic =ᶠ[𝓝 y] scalarRegularDerivativeSeries m := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
      exact ih ht
    rw [he.deriv_eq]
    exact (scalarRegularDerivativeSeries_hasDerivAt m hy).deriv

/-- The first printed regularized-cosecant derivative identity on p. 36. -/
theorem scalar_regular_second_derivative_identity :
    iteratedDeriv 2 scalarRegularAnalytic 1 +
      2 * iteratedDeriv 1 scalarRegularAnalytic 1 = Real.pi ^ 2 / 4 := by
  rw [scalarRegularAnalytic_iteratedDeriv 2 (by norm_num),
    scalarRegularAnalytic_iteratedDeriv 1 (by norm_num)]
  exact scalarRegularDerivativeSeries_second_add_twice_first

/-- The second printed regularized-cosecant derivative identity on p. 36. -/
theorem scalar_regular_third_derivative_identity :
    iteratedDeriv 3 scalarRegularAnalytic 1 +
      3 * iteratedDeriv 2 scalarRegularAnalytic 1 = 3 * Real.pi ^ 2 / 4 := by
  rw [scalarRegularAnalytic_iteratedDeriv 3 (by norm_num),
    scalarRegularAnalytic_iteratedDeriv 2 (by norm_num)]
  exact scalarRegularDerivativeSeries_third_add_three_second

theorem scalarPhiTerm_third_one_regular (i : ℕ) :
    scalarPhiTerm i 3 1 =
      -3 * (scalarRegularDerivativeTerm i 2 1 + 2 * scalarRegularDerivativeTerm i 1 1) := by
  have he := scalar_third_power_difference_one (2 * i + 1)
  rw [show 2 * i + 1 + 1 = 2 * i + 2 by omega,
    show 2 * i + 1 + 2 = 2 * i + 3 by omega] at he
  rw [scalarPhiTerm, he]
  simp only [scalarRegularDerivativeTerm, scalarPowerDerivative, one_pow, mul_one,
    Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, Nat.cast_mul,
    Nat.cast_one, Nat.cast_sub (by omega : 1 ≤ 2 * i + 1)]
  push_cast
  ring

theorem scalarPhiTerm_fourth_one_regular (i : ℕ) :
    scalarPhiTerm i 4 1 =
      -4 * (scalarRegularDerivativeTerm i 3 1 + 3 * scalarRegularDerivativeTerm i 2 1) := by
  by_cases hi : i = 0
  · subst i
    norm_num [scalarPhiTerm, scalarRegularDerivativeTerm, scalarPowerDerivative, Nat.descFactorial_succ]
  have he := scalar_fourth_power_difference_one (2 * i + 1)
  rw [show 2 * i + 1 + 1 = 2 * i + 2 by omega,
    show 2 * i + 1 + 2 = 2 * i + 3 by omega] at he
  rw [scalarPhiTerm, he]
  simp only [scalarRegularDerivativeTerm, scalarPowerDerivative, one_pow, mul_one,
    Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, Nat.cast_mul,
    Nat.cast_one, Nat.cast_sub (by omega : 1 ≤ 2 * i + 1),
    Nat.cast_sub (by omega : 2 ≤ 2 * i + 1)]
  push_cast
  ring

theorem scalarPhiSeries_third_one : scalarPhiSeries 3 1 = -(3 * Real.pi ^ 2 / 4) := by
  have h2 := (scalarRegularDerivativeTerm_summable 2
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) (3 / 2))).hasSum
  have h1 := (scalarRegularDerivativeTerm_summable 1
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) (3 / 2))).hasSum
  have hs : HasSum (fun i => scalarPhiTerm i 3 1)
      (-3 * (scalarRegularDerivativeSeries 2 1 + 2 * scalarRegularDerivativeSeries 1 1)) := by
    simpa only [scalarPhiTerm_third_one_regular, scalarRegularDerivativeSeries] using
      (h2.add (h1.mul_left 2)).mul_left (-3)
  rw [scalarPhiSeries, hs.tsum_eq, scalarRegularDerivativeSeries_second_add_twice_first]
  ring

theorem scalarPhiSeries_fourth_one : scalarPhiSeries 4 1 = -(3 * Real.pi ^ 2) := by
  have h3 := (scalarRegularDerivativeTerm_summable 3
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) (3 / 2))).hasSum
  have h2 := (scalarRegularDerivativeTerm_summable 2
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) (3 / 2))).hasSum
  have hs : HasSum (fun i => scalarPhiTerm i 4 1)
      (-4 * (scalarRegularDerivativeSeries 3 1 + 3 * scalarRegularDerivativeSeries 2 1)) := by
    simpa only [scalarPhiTerm_fourth_one_regular, scalarRegularDerivativeSeries] using
      (h3.add (h2.mul_left 3)).mul_left (-4)
  rw [scalarPhiSeries, hs.tsum_eq, scalarRegularDerivativeSeries_third_add_three_second]
  ring

/-- The sharp uniform third-derivative bound printed after (I.5). -/
theorem scalarPhiSeries_third_bound {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    |scalarPhiSeries 3 y| ≤ 3 * Real.pi ^ 2 / 4 := by
  simpa only [scalarPhiSeries_third_one, neg_neg] using
    scalarPhiSeries_third_bound_endpoint hy

/-- The sharp uniform fourth-derivative bound printed after (I.5). -/
theorem scalarPhiSeries_fourth_bound {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    |scalarPhiSeries 4 y| ≤ 3 * Real.pi ^ 2 := by
  simpa only [scalarPhiSeries_fourth_one, neg_neg] using
    scalarPhiSeries_fourth_bound_endpoint hy

/-- The literal phi from Appendix I, using the removable regularized cosecant. -/
def scalarSteinPhi (y : ℝ) : ℝ := y * (1 - y) * scalarRegularAnalytic y

theorem scalarSteinPhi_eq_series {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    scalarSteinPhi y = scalarPhiSeries 0 y := by
  have hs := scalar_regular_sin_ne_zero
    (show y ∈ Ioo (0 : ℝ) (3 / 2) from ⟨hy.1, by linarith [hy.2]⟩)
  have hy0 : y ≠ 0 := hy.1.ne'
  rw [scalarPhiSeries_zero_order ⟨hy.1.le, hy.2.le⟩,
    scalarSteinPhi, scalarRegularAnalytic,
    show Real.pi * y / 2 = (Real.pi / 2) * y by ring]
  field_simp [hs, hy0, Real.pi_ne_zero]
  <;> ring

/-- Actual third derivatives on the open interval; the preceding series bound
also controls the continuous derivative-series values at both endpoints. -/
theorem scalar_stein_third_derivative_bound {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    |iteratedDeriv 3 scalarSteinPhi y| ≤ 3 * Real.pi ^ 2 / 4 := by
  have he : scalarSteinPhi =ᶠ[𝓝 y] scalarPhiSeries 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact scalarSteinPhi_eq_series ht
  rw [Filter.EventuallyEq.iteratedDeriv_eq 3 he, scalarPhiSeries_iteratedDeriv 3 hy]
  exact scalarPhiSeries_third_bound ⟨hy.1.le, hy.2.le⟩

theorem scalar_stein_fourth_derivative_bound {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    |iteratedDeriv 4 scalarSteinPhi y| ≤ 3 * Real.pi ^ 2 := by
  have he : scalarSteinPhi =ᶠ[𝓝 y] scalarPhiSeries 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact scalarSteinPhi_eq_series ht
  rw [Filter.EventuallyEq.iteratedDeriv_eq 4 he, scalarPhiSeries_iteratedDeriv 4 hy]
  exact scalarPhiSeries_fourth_bound ⟨hy.1.le, hy.2.le⟩

end

end CGLMPBounds.Certificates
