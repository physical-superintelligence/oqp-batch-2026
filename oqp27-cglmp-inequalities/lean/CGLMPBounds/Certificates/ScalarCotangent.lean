module

public import CGLMPBounds.Certificates.ScalarEta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

@[expose] public section


/-!
# Cotangent series underlying the source cosecant coefficients

The Mittag-Leffler expansion is reused from pinned Mathlib. Its geometric
expansion is justified by nonnegative double summation, including an explicit
summability proof.
-/

namespace CGLMPBounds.Certificates

lemma real_mem_integerComplement {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (x : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hr := congrArg Complex.re hn
  simp only [Complex.intCast_re, Complex.ofReal_re] at hr
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith [hx.1])
  have hn1 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith [hx.2])
  omega

/-- The real Mittag-Leffler expansion, with paired poles so it is summable. -/
theorem real_cotangent_hasSum {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (x - ((n : ℝ) + 1)) + 1 / (x + ((n : ℝ) + 1)))
      (Real.pi * Real.cot (Real.pi * x) - 1 / x) := by
  have hz := real_mem_integerComplement hx
  have h := (summable_cotTerm hz).hasSum
  rw [← cot_series_rep' hz] at h
  have hc (n : ℕ) : cotTerm (x : ℂ) n =
      ((1 / (x - ((n : ℝ) + 1)) + 1 / (x + ((n : ℝ) + 1)) : ℝ) : ℂ) := by
    simp only [cotTerm, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_natCast]
  have hs : (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (x : ℂ)) - 1 / (x : ℂ) =
      ((Real.pi * Real.cot (Real.pi * x) - 1 / x : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_cot,
      Complex.ofReal_div, Complex.ofReal_one]
  simpa only [hc, hs, Complex.ofReal_re] using Complex.hasSum_re h

lemma cotangent_paired_pole {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    1 / (x - ((n : ℝ) + 1)) + 1 / (x + ((n : ℝ) + 1)) =
      -2 * (x / (((n : ℝ) + 1) ^ 2 - x ^ 2)) := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hm : x - ((n : ℝ) + 1) ≠ 0 := by linarith [hx.2]
  have hp : x + ((n : ℝ) + 1) ≠ 0 := by linarith [hx.1]
  have hd : ((n : ℝ) + 1) ^ 2 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  field_simp [hm, hp, hd]
  <;> ring

theorem cotangent_resolvent_hasSum {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ => x / (((n : ℝ) + 1) ^ 2 - x ^ 2))
      ((1 / x - Real.pi * Real.cot (Real.pi * x)) / 2) := by
  have h := (real_cotangent_hasSum hx).mul_left (-(1 : ℝ) / 2)
  convert h using 1
  · ext n
    rw [cotangent_paired_pole hx]
    ring
  · ring

/-- Expand a single positive denominator by its convergent geometric series. -/
theorem cotangent_geometric_row {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    HasSum (fun k : ℕ => x ^ (2 * k + 1) / ((n : ℝ) + 1) ^ (2 * k + 2))
      (x / (((n : ℝ) + 1) ^ 2 - x ^ 2)) := by
  let a : ℝ := (n : ℝ) + 1
  have ha : 1 ≤ a := by dsimp [a]; exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have ha0 : a ≠ 0 := by linarith
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha0
  have hratio0 : 0 ≤ x ^ 2 / a ^ 2 := by positivity
  have hratio : |x ^ 2 / a ^ 2| < 1 := by
    rw [abs_of_nonneg hratio0, div_lt_one ha2]
    nlinarith [hx.1, hx.2]
  have h := (hasSum_geometric_of_abs_lt_one hratio).mul_right (x / a ^ 2)
  have hden : a ^ 2 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  convert h using 1
  · ext k
    change x ^ (2 * k + 1) / a ^ (2 * k + 2) = (x ^ 2 / a ^ 2) ^ k * (x / a ^ 2)
    rw [div_pow, ← pow_mul, ← pow_mul, pow_add, pow_add]
    simp only [pow_one]
    field_simp
  · change x / (a ^ 2 - x ^ 2) = (1 - x ^ 2 / a ^ 2)⁻¹ * (x / a ^ 2)
    field_simp [ha0, hden]
    <;> ring

/-- Absolute summability of the double geometric expansion (all its terms are
nonnegative on this interval). This is the justification for exchanging sums. -/
theorem cotangent_double_summable {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun p : ℕ × ℕ => x ^ (2 * p.2 + 1) / ((p.1 : ℝ) + 1) ^ (2 * p.2 + 2)) := by
  have hx0 : 0 ≤ x := hx.1.le
  apply (summable_prod_of_nonneg (by intro p; positivity)).2
  refine ⟨fun n => (cotangent_geometric_row hx n).summable, ?_⟩
  simpa only [(cotangent_geometric_row hx _).tsum_eq] using
    (cotangent_resolvent_hasSum hx).summable

lemma cotangent_column_tsum {x : ℝ} (k : ℕ) :
    (∑' n : ℕ, x ^ (2 * k + 1) / ((n : ℝ) + 1) ^ (2 * k + 2)) =
      x ^ (2 * k + 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * (k + 1)) := by
  have hn : k + 1 ≠ 0 := by omega
  have hf := scalar_reciprocal_power_summable (k + 1) hn
  have hz : (1 : ℝ) / (0 : ℝ) ^ (2 * (k + 1)) = 0 := by simp
  have hshift : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 * (k + 1))) =
      ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * (k + 1)) := by
    simpa only [Nat.cast_zero, hz, zero_add, Nat.cast_add, Nat.cast_one] using
      hf.tsum_eq_zero_add.symm
  rw [show 2 * k + 2 = 2 * (k + 1) by omega]
  calc
    _ = ∑' n : ℕ, x ^ (2 * k + 1) * (1 / ((n : ℝ) + 1) ^ (2 * (k + 1))) := by
      apply tsum_congr
      intro n
      ring
    _ = _ := by rw [tsum_mul_left, hshift]

/-- Cotangent's convergent zeta-coefficient power series, derived analytically
from the paired-pole sum and justified interchange of the two summations. -/
theorem cotangent_power_hasSum {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ => x ^ (2 * k + 1) *
      ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * (k + 1)))
      ((1 / x - Real.pi * Real.cot (Real.pi * x)) / 2) := by
  let f : ℕ → ℕ → ℝ := fun n k =>
    x ^ (2 * k + 1) / ((n : ℝ) + 1) ^ (2 * k + 2)
  have hf : Summable (Function.uncurry f) := cotangent_double_summable hx
  have hs : Summable (fun k => ∑' n, f n k) := hf.prod_symm.prod
  have heq : (∑' k, ∑' n, f n k) =
      (1 / x - Real.pi * Real.cot (Real.pi * x)) / 2 := by
    rw [hf.tsum_comm]
    simpa only [f, (cotangent_geometric_row hx _).tsum_eq] using
      (cotangent_resolvent_hasSum hx).tsum_eq
  have h := hs.hasSum
  rw [heq] at h
  simpa only [f, cotangent_column_tsum] using h

end CGLMPBounds.Certificates
