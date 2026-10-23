module

public import CGLMPBounds.Certificates.ScalarSmooth
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section


/-!
# Sharp polynomial derivative bounds for the beta–Stein estimate

Canonical supplement p. 36, following (I.5). The third and fourth derivatives
of `y^(k+1)-y^(k+2)` have respective bounds `3*k*(k+1)` and
`4*k*(k-1)*(k+1)` on `[0,1]`. Their largest absolute values occur at one.
Positivity of the actual cosecant coefficients transfers these sharp bounds to
the derivative series, whose suprema reduce to their values at one.

The final numerical evaluations of those series as `3*pi^2/4` and `3*pi^2`
are separate obligations; they are not assumed below.

Reuse: Mathlib's iterated derivative of a power and subtraction rule identify
the source polynomial derivatives. The cap estimate below follows by a finite
induction with decrement `(m+1)*y^m*(1-y)^2`, avoiding a separate geometric-sum
argument. `tsum_of_norm_bounded` transfers the term bounds to genuine convergent
series supplied by `ScalarSmooth`.
-/

namespace CGLMPBounds.Certificates

open Filter Set
open scoped Topology

noncomputable section

/-- The elementary cap estimate used on the positive side of each derivative. -/
theorem scalar_power_cap (m : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    y ^ m * ((m : ℝ) + 1 - (m : ℝ) * y) ≤ 1 := by
  have hy0 : 0 ≤ y := hy.1
  induction m with
  | zero => simp
  | succ m ih =>
    have hdec : 0 ≤ ((m : ℝ) + 1) * y ^ m * (1 - y) ^ 2 := by positivity
    calc
      y ^ (m + 1) * (((m + 1 : ℕ) : ℝ) + 1 - ((m + 1 : ℕ) : ℝ) * y)
          = y ^ m * ((m : ℝ) + 1 - (m : ℝ) * y) -
              ((m : ℝ) + 1) * y ^ m * (1 - y) ^ 2 := by
            rw [pow_succ]
            push_cast
            ring
      _ ≤ y ^ m * ((m : ℝ) + 1 - (m : ℝ) * y) := sub_le_self _ hdec
      _ ≤ 1 := ih

/-- Both signs of the polynomial factor. For r≥1 its negative endpoint gives
the sharp absolute bound r. -/
theorem scalar_power_linear_abs_bound (m : ℕ) (r : ℝ) (hr : 1 ≤ r)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    |y ^ m * ((m : ℝ) + 1 - ((m : ℝ) + 1 + r) * y)| ≤ r := by
  have hy0 : 0 ≤ y := hy.1
  have hy1 : 0 ≤ 1 - y := sub_nonneg.mpr hy.2
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hpow : y ^ (m + 1) ≤ 1 := pow_le_one₀ hy.1 hy.2
  have hrpow : r * y ^ (m + 1) ≤ r := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hr0
  have hpos : 0 ≤ y ^ m * ((m : ℝ) + 1) * (1 - y) := by positivity
  have hsub : 0 ≤ (1 + r) * y ^ (m + 1) := by positivity
  rw [abs_le]
  constructor
  · have he : y ^ m * ((m : ℝ) + 1 - ((m : ℝ) + 1 + r) * y) =
        y ^ m * ((m : ℝ) + 1) * (1 - y) - r * y ^ (m + 1) := by
      rw [pow_succ]
      ring
    rw [he]
    linarith
  · calc
      y ^ m * ((m : ℝ) + 1 - ((m : ℝ) + 1 + r) * y)
          = y ^ m * ((m : ℝ) + 1 - (m : ℝ) * y) -
              (1 + r) * y ^ (m + 1) := by rw [pow_succ]; ring
      _ ≤ y ^ m * ((m : ℝ) + 1 - (m : ℝ) * y) := sub_le_self _ hsub
      _ ≤ 1 := scalar_power_cap m hy
      _ ≤ r := hr

theorem scalar_third_power_difference_factor (m : ℕ) (y : ℝ) :
    scalarPowerDerivative (m + 3) 3 y - scalarPowerDerivative (m + 4) 3 y =
      ((m : ℝ) + 2) * ((m : ℝ) + 3) *
        (y ^ m * ((m : ℝ) + 1 - ((m : ℝ) + 4) * y)) := by
  simp only [scalarPowerDerivative, Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.sub_zero, mul_one,
    show m + 3 - 1 = m + 2 by omega,
    show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega,
    show m + 4 - 1 = m + 3 by omega,
    show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  push_cast
  rw [pow_succ]
  ring

theorem scalar_fourth_power_difference_factor (m : ℕ) (y : ℝ) :
    scalarPowerDerivative (m + 4) 4 y - scalarPowerDerivative (m + 5) 4 y =
      ((m : ℝ) + 3) * ((m : ℝ) + 2) * ((m : ℝ) + 4) *
        (y ^ m * ((m : ℝ) + 1 - ((m : ℝ) + 5) * y)) := by
  simp only [scalarPowerDerivative, Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.sub_zero, mul_one,
    show m + 4 - 1 = m + 3 by omega,
    show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega,
    show m + 4 - 4 = m by omega,
    show m + 5 - 1 = m + 4 by omega,
    show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega,
    show m + 5 - 4 = m + 1 by omega]
  push_cast
  rw [pow_succ]
  ring

/-- The source's third-derivative bound, valid even for k=0. -/
theorem scalar_third_power_difference_bound (k : ℕ) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    |scalarPowerDerivative (k + 1) 3 y - scalarPowerDerivative (k + 2) 3 y| ≤
      3 * (k : ℝ) * ((k : ℝ) + 1) := by
  by_cases hk : k < 2
  · interval_cases k <;> norm_num [scalarPowerDerivative, Nat.descFactorial_succ]
  · let m := k - 2
    have hkm : k = m + 2 := by dsimp [m]; omega
    rw [hkm, show m + 2 + 1 = m + 3 by omega,
      show m + 2 + 2 = m + 4 by omega, scalar_third_power_difference_factor]
    have hc : 0 ≤ ((m : ℝ) + 2) * ((m : ℝ) + 3) := by positivity
    rw [abs_mul, abs_of_nonneg hc]
    have hb : |y ^ m * ((m : ℝ) + 1 - ((m : ℝ) + 4) * y)| ≤ 3 := by
      simpa only [show (m : ℝ) + 1 + 3 = (m : ℝ) + 4 by ring] using
        scalar_power_linear_abs_bound m 3 (by norm_num) hy
    convert mul_le_mul_of_nonneg_left hb hc using 1 <;> push_cast <;> ring

/-- The source's fourth-derivative bound, including the vanishing k=1 case. -/
theorem scalar_fourth_power_difference_bound (k : ℕ) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    |scalarPowerDerivative (k + 1) 4 y - scalarPowerDerivative (k + 2) 4 y| ≤
      4 * (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) + 1) := by
  by_cases hk : k < 3
  · interval_cases k <;> norm_num [scalarPowerDerivative, Nat.descFactorial_succ]
  · let m := k - 3
    have hkm : k = m + 3 := by dsimp [m]; omega
    rw [hkm, show m + 3 + 1 = m + 4 by omega,
      show m + 3 + 2 = m + 5 by omega, scalar_fourth_power_difference_factor]
    have hc : 0 ≤ ((m : ℝ) + 3) * ((m : ℝ) + 2) * ((m : ℝ) + 4) := by positivity
    rw [abs_mul, abs_of_nonneg hc]
    have hb : |y ^ m * ((m : ℝ) + 1 - ((m : ℝ) + 5) * y)| ≤ 4 := by
      simpa only [show (m : ℝ) + 1 + 4 = (m : ℝ) + 5 by ring] using
        scalar_power_linear_abs_bound m 4 (by norm_num) hy
    convert mul_le_mul_of_nonneg_left hb hc using 1 <;> push_cast <;> ring

/-- Identification with actual iterated derivatives of the source polynomial. -/
theorem scalar_power_difference_iteratedDeriv (k m : ℕ) (y : ℝ) :
    iteratedDeriv m (fun t : ℝ => t ^ (k + 1) - t ^ (k + 2)) y =
      scalarPowerDerivative (k + 1) m y - scalarPowerDerivative (k + 2) m y := by
  rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_pow, scalarPowerDerivative]

theorem scalar_stein_third_polynomial_bound (k : ℕ) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDeriv 3 (fun t : ℝ => t ^ (k + 1) - t ^ (k + 2)) y| ≤
      3 * (k : ℝ) * ((k : ℝ) + 1) := by
  rw [scalar_power_difference_iteratedDeriv]
  exact scalar_third_power_difference_bound k hy

theorem scalar_stein_fourth_polynomial_bound (k : ℕ) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDeriv 4 (fun t : ℝ => t ^ (k + 1) - t ^ (k + 2)) y| ≤
      4 * (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) + 1) := by
  rw [scalar_power_difference_iteratedDeriv]
  exact scalar_fourth_power_difference_bound k hy

theorem scalar_third_power_difference_one (k : ℕ) :
    scalarPowerDerivative (k + 1) 3 1 - scalarPowerDerivative (k + 2) 3 1 =
      -(3 * (k : ℝ) * ((k : ℝ) + 1)) := by
  by_cases hk : k < 2
  · interval_cases k <;> norm_num [scalarPowerDerivative, Nat.descFactorial_succ]
  · let m := k - 2
    have hkm : k = m + 2 := by dsimp [m]; omega
    rw [hkm, show m + 2 + 1 = m + 3 by omega,
      show m + 2 + 2 = m + 4 by omega, scalar_third_power_difference_factor]
    simp only [one_pow, one_mul, mul_one]
    push_cast
    ring

theorem scalar_fourth_power_difference_one (k : ℕ) :
    scalarPowerDerivative (k + 1) 4 1 - scalarPowerDerivative (k + 2) 4 1 =
      -(4 * (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) + 1)) := by
  by_cases hk : k < 3
  · interval_cases k <;> norm_num [scalarPowerDerivative, Nat.descFactorial_succ]
  · let m := k - 3
    have hkm : k = m + 3 := by dsimp [m]; omega
    rw [hkm, show m + 3 + 1 = m + 4 by omega,
      show m + 3 + 2 = m + 5 by omega, scalar_fourth_power_difference_factor]
    simp only [one_pow, one_mul, mul_one]
    push_cast
    ring

/-- Positivity of r_n makes the absolute bound equal to minus the term at one. -/
theorem scalarPhiTerm_third_bound_endpoint (i : ℕ) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    ‖scalarPhiTerm i 3 y‖ ≤ -scalarPhiTerm i 3 1 := by
  have hc : 0 ≤ scalarCosecantCoefficient (i + 1) :=
    (scalarCosecantCoefficient_pos_lt (i + 1) (by omega)).1.le
  have hb := scalar_third_power_difference_bound (2 * i + 1) hy
  have he := scalar_third_power_difference_one (2 * i + 1)
  rw [show 2 * i + 1 + 1 = 2 * i + 2 by omega,
    show 2 * i + 1 + 2 = 2 * i + 3 by omega] at hb he
  rw [scalarPhiTerm, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc,
    scalarPhiTerm, he]
  convert mul_le_mul_of_nonneg_left hb hc using 1 <;> ring

theorem scalarPhiTerm_fourth_bound_endpoint (i : ℕ) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    ‖scalarPhiTerm i 4 y‖ ≤ -scalarPhiTerm i 4 1 := by
  have hc : 0 ≤ scalarCosecantCoefficient (i + 1) :=
    (scalarCosecantCoefficient_pos_lt (i + 1) (by omega)).1.le
  have hb := scalar_fourth_power_difference_bound (2 * i + 1) hy
  have he := scalar_fourth_power_difference_one (2 * i + 1)
  rw [show 2 * i + 1 + 1 = 2 * i + 2 by omega,
    show 2 * i + 1 + 2 = 2 * i + 3 by omega] at hb he
  rw [scalarPhiTerm, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc,
    scalarPhiTerm, he]
  convert mul_le_mul_of_nonneg_left hb hc using 1 <;> ring

/-- Uniform third-derivative series bound reduced to its genuine endpoint sum. -/
theorem scalarPhiSeries_third_bound_endpoint {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    |scalarPhiSeries 3 y| ≤ -scalarPhiSeries 3 1 := by
  have hs : HasSum (fun i => -scalarPhiTerm i 3 1) (-scalarPhiSeries 3 1) := by
    simpa only [scalarPhiSeries] using
      (scalarPhiTerm_summable 3 (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)).hasSum.neg
  simpa only [scalarPhiSeries, Real.norm_eq_abs] using
    tsum_of_norm_bounded hs (fun i => scalarPhiTerm_third_bound_endpoint i hy)

theorem scalarPhiSeries_fourth_bound_endpoint {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    |scalarPhiSeries 4 y| ≤ -scalarPhiSeries 4 1 := by
  have hs : HasSum (fun i => -scalarPhiTerm i 4 1) (-scalarPhiSeries 4 1) := by
    simpa only [scalarPhiSeries] using
      (scalarPhiTerm_summable 4 (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)).hasSum.neg
  simpa only [scalarPhiSeries, Real.norm_eq_abs] using
    tsum_of_norm_bounded hs (fun i => scalarPhiTerm_fourth_bound_endpoint i hy)

/-- The derivative-series values extend continuously to the closed interval. -/
theorem scalarPhiSeries_continuousOn_unit (m : ℕ) :
    ContinuousOn (scalarPhiSeries m) (Icc (0 : ℝ) 1) := by
  exact continuousOn_tsum (f := fun i y => scalarPhiTerm i m y)
    (fun i => by
      apply Continuous.continuousOn
      unfold scalarPhiTerm scalarPowerDerivative
      fun_prop)
    (scalarPhiMajorant_summable m) (fun i y hy => scalarPhiTerm_bound i m hy)

/-- On the open unit interval these series are the actual derivatives of phi. -/
theorem scalarPhiSeries_iteratedDeriv (m : ℕ) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    iteratedDeriv m (scalarPhiSeries 0) y = scalarPhiSeries m y := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv m (scalarPhiSeries 0) =ᶠ[𝓝 y] scalarPhiSeries m := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
      exact ih ht
    rw [he.deriv_eq]
    exact (scalarPhiSeries_hasDerivAt m hy).deriv

end

end CGLMPBounds.Certificates
