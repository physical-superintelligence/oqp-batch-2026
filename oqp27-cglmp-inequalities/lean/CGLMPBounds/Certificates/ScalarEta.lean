module

public import CGLMPBounds.Defs.ScalarEta
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section


/-!
# The alternating series in Appendix J

We reuse Mathlib's even zeta-value formula and alternating-series bounds.
The Bernoulli/eta identity and cosecant generating function are separate bridges.
-/

namespace CGLMPBounds.Certificates

open Finset

theorem scalar_reciprocal_power_summable (n : ℕ) (hn : n ≠ 0) :
    Summable (fun j : ℕ => 1 / (j : ℝ) ^ (2 * n)) :=
  (hasSum_zeta_nat hn).summable

theorem scalar_reciprocal_shift_summable (n : ℕ) (hn : n ≠ 0) :
    Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ (2 * n)) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 (scalar_reciprocal_power_summable n hn)

theorem scalarEta_summable (n : ℕ) (hn : n ≠ 0) :
    Summable (fun j : ℕ => (-1 : ℝ) ^ j * (1 / ((j : ℝ) + 1) ^ (2 * n))) :=
  (scalar_reciprocal_shift_summable n hn).alternating

/-- The strict eta interval in the supplement, proved from the first two and
first three partial sums of an antitone alternating series. -/
theorem scalarEta_mem_Ioo (n : ℕ) (hn : n ≠ 0) : scalarEta n ∈ Set.Ioo (0 : ℝ) 1 := by
  have hp : 2 * n ≠ 0 := by omega
  have hanti : Antitone (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ (2 * n)) := by
    intro a b hab
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right hab 1
  have hlim := (scalar_reciprocal_shift_summable n hn).tendsto_alternating_series_tsum
  have hl := Antitone.alternating_series_le_tendsto hlim hanti 1
  have hu := Antitone.tendsto_le_alternating_series hlim hanti 1
  change _ ≤ scalarEta n at hl
  change scalarEta n ≤ _ at hu
  norm_num [Finset.sum_range_succ] at hl hu
  have htwo : (1 : ℝ) < 2 ^ (2 * n) := one_lt_pow₀ (by norm_num) hp
  have hpow : (2 : ℝ) ^ (2 * n) < 3 ^ (2 * n) :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) hp
  have hrecip : (1 : ℝ) / 2 ^ (2 * n) < 1 := by
    exact (div_lt_one (by positivity)).2 htwo
  have hrecip23 : (1 : ℝ) / 3 ^ (2 * n) < 1 / 2 ^ (2 * n) :=
    one_div_lt_one_div_of_lt (by positivity) hpow
  simp only [one_div] at hrecip hrecip23
  constructor <;> linarith

/-- Splitting the positive zeta series and its alternating version into even
and odd indices gives the eta/zeta factor without a quoted analytic identity. -/
theorem scalarEta_eq_zeta_factor (n : ℕ) (hn : n ≠ 0) :
    scalarEta n = (1 - 2 / (2 : ℝ) ^ (2 * n)) *
      ∑' j : ℕ, 1 / (j : ℝ) ^ (2 * n) := by
  let f : ℕ → ℝ := fun j => 1 / (j : ℝ) ^ (2 * n)
  have hf : Summable f := scalar_reciprocal_power_summable n hn
  have hf0 : f 0 = 0 := by simp [f, hn]
  have hfs : Summable (fun j => f (j + 1)) := (summable_nat_add_iff 1).2 hf
  have he : Summable (fun j => f (2 * j)) :=
    hf.comp_injective (by intro a b hab; omega)
  have ho : Summable (fun j => f (2 * j + 1)) :=
    hf.comp_injective (by
      intro a b hab
      change 2 * a + 1 = 2 * b + 1 at hab
      omega)
  have hsplit := tsum_even_add_odd he ho
  have heq : (∑' j, f (2 * j)) = (1 / (2 : ℝ) ^ (2 * n)) * ∑' j, f j := by
    calc
      _ = ∑' j, (1 / (2 : ℝ) ^ (2 * n)) * f j := by
        apply tsum_congr
        intro j
        simp [f, Nat.cast_mul, mul_pow, mul_comm]
      _ = _ := tsum_mul_left
  have hshift : (∑' j, f (j + 1)) = ∑' j, f j := by
    simpa only [hf0, zero_add] using hf.tsum_eq_zero_add.symm
  have hE : (∑' j, f (2 * j + 2)) = (1 / (2 : ℝ) ^ (2 * n)) * ∑' j, f j := by
    calc
      _ = ∑' j, (1 / (2 : ℝ) ^ (2 * n)) * f (j + 1) := by
        apply tsum_congr
        intro j
        rw [show 2 * j + 2 = 2 * (j + 1) by omega]
        simp [f, Nat.cast_mul, mul_pow, mul_comm]
      _ = _ := by rw [tsum_mul_left, hshift]
  let g : ℕ → ℝ := fun j => (-1 : ℝ) ^ j * f (j + 1)
  have hg : Summable g := hfs.alternating
  have hge : Summable (fun j => g (2 * j)) :=
    hg.comp_injective (by intro a b hab; omega)
  have hgo : Summable (fun j => g (2 * j + 1)) :=
    hg.comp_injective (by
      intro a b hab
      change 2 * a + 1 = 2 * b + 1 at hab
      omega)
  have hsplitg := tsum_even_add_odd hge hgo
  have hgeq : (∑' j, g (2 * j)) = ∑' j, f (2 * j + 1) := by
    apply tsum_congr
    intro j
    simp [g, pow_mul]
  have hgoq : (∑' j, g (2 * j + 1)) = -(∑' j, f (2 * j + 2)) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro j
    simp [g, pow_add, pow_mul, Nat.add_assoc]
  have hgEta : (∑' j, g j) = scalarEta n := by
    simp only [g, f, scalarEta, Nat.cast_add, Nat.cast_one]
  rw [heq] at hsplit
  rw [hgeq, hgoq, hE, hgEta] at hsplitg
  change scalarEta n = (1 - 2 / (2 : ℝ) ^ (2 * n)) * ∑' j, f j
  simp only [div_eq_mul_inv, one_mul] at hsplit hsplitg ⊢
  linear_combination hsplit - hsplitg

/-- Absolute value removes the parity sign in Mathlib's even-zeta formula. -/
theorem scalar_zeta_eq_abs_bernoulli (n : ℕ) (hn : n ≠ 0) :
    (∑' j : ℕ, 1 / (j : ℝ) ^ (2 * n)) =
      (2 : ℝ) ^ (2 * n - 1) * Real.pi ^ (2 * n) *
        |(bernoulli (2 * n) : ℝ)| / ((2 * n).factorial : ℝ) := by
  have h := congrArg abs (hasSum_zeta_nat hn).tsum_eq
  have hz : 0 ≤ ∑' j : ℕ, 1 / (j : ℝ) ^ (2 * n) := by
    apply tsum_nonneg
    intro j
    positivity
  simpa only [abs_of_nonneg hz, abs_div, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg Real.pi_pos.le,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) ((2 * n).factorial))] using h

end CGLMPBounds.Certificates
