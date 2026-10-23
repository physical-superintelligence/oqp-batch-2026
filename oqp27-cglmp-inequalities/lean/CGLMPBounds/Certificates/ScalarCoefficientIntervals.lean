module

public import CGLMPBounds.Defs.ScalarCertificateData
public import CGLMPBounds.Defs.ScalarCoefficients
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section


/-!
# The ten exact coefficient enclosures of Table J.1

Generated rational witnesses are checked in Lean. The Bernoulli values below
are derived from Mathlib's recurrence, and the real enclosures use Mathlib's
proved twenty-decimal pi bounds. No floating-point result is a proof input.
The analytic cosecant expansion remains a separate theorem.
-/

namespace CGLMPBounds.Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem bernoulliPositive_0 : bernoulli' 0 = (1 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial]

private theorem bernoulliPositive_1 : bernoulli' 1 = ((1 / 2) : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0]

private theorem bernoulliPositive_2 : bernoulli' 2 = ((1 / 6) : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1]

private theorem bernoulliPositive_3 : bernoulli' 3 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2]

private theorem bernoulliPositive_4 : bernoulli' 4 = ((-1 / 30) : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3]

private theorem bernoulliPositive_5 : bernoulli' 5 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4]

private theorem bernoulliPositive_6 : bernoulli' 6 = ((1 / 42) : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5]

private theorem bernoulliPositive_7 : bernoulli' 7 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6]

private theorem bernoulliPositive_8 : bernoulli' 8 = ((-1 / 30) : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7]

private theorem bernoulliPositive_9 : bernoulli' 9 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7, bernoulliPositive_8]

private theorem bernoulliPositive_10 : bernoulli' 10 = ((5 / 66) : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7, bernoulliPositive_8, bernoulliPositive_9]

private theorem bernoulliPositive_11 : bernoulli' 11 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7, bernoulliPositive_8, bernoulliPositive_9, bernoulliPositive_10]

private theorem bernoulliPositive_12 : bernoulli' 12 = ((-691 / 2730) : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7, bernoulliPositive_8, bernoulliPositive_9, bernoulliPositive_10, bernoulliPositive_11]

private theorem bernoulliPositive_13 : bernoulli' 13 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7, bernoulliPositive_8, bernoulliPositive_9, bernoulliPositive_10, bernoulliPositive_11, bernoulliPositive_12]

private theorem bernoulliPositive_14 : bernoulli' 14 = ((7 / 6) : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7, bernoulliPositive_8, bernoulliPositive_9, bernoulliPositive_10, bernoulliPositive_11, bernoulliPositive_12, bernoulliPositive_13]

private theorem bernoulliPositive_15 : bernoulli' 15 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7, bernoulliPositive_8, bernoulliPositive_9, bernoulliPositive_10, bernoulliPositive_11, bernoulliPositive_12, bernoulliPositive_13, bernoulliPositive_14]

private theorem bernoulliPositive_16 : bernoulli' 16 = ((-3617 / 510) : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7, bernoulliPositive_8, bernoulliPositive_9, bernoulliPositive_10, bernoulliPositive_11, bernoulliPositive_12, bernoulliPositive_13, bernoulliPositive_14, bernoulliPositive_15]

private theorem bernoulliPositive_17 : bernoulli' 17 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7, bernoulliPositive_8, bernoulliPositive_9, bernoulliPositive_10, bernoulliPositive_11, bernoulliPositive_12, bernoulliPositive_13, bernoulliPositive_14, bernoulliPositive_15, bernoulliPositive_16]

private theorem bernoulliPositive_18 : bernoulli' 18 = ((43867 / 798) : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7, bernoulliPositive_8, bernoulliPositive_9, bernoulliPositive_10, bernoulliPositive_11, bernoulliPositive_12, bernoulliPositive_13, bernoulliPositive_14, bernoulliPositive_15, bernoulliPositive_16, bernoulliPositive_17]

private theorem bernoulliPositive_19 : bernoulli' 19 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7, bernoulliPositive_8, bernoulliPositive_9, bernoulliPositive_10, bernoulliPositive_11, bernoulliPositive_12, bernoulliPositive_13, bernoulliPositive_14, bernoulliPositive_15, bernoulliPositive_16, bernoulliPositive_17, bernoulliPositive_18]

private theorem bernoulliPositive_20 : bernoulli' 20 = ((-174611 / 330) : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_fast_choose, Nat.fast_choose, Nat.descFactorial, Nat.factorial, bernoulliPositive_0, bernoulliPositive_1, bernoulliPositive_2, bernoulliPositive_3, bernoulliPositive_4, bernoulliPositive_5, bernoulliPositive_6, bernoulliPositive_7, bernoulliPositive_8, bernoulliPositive_9, bernoulliPositive_10, bernoulliPositive_11, bernoulliPositive_12, bernoulliPositive_13, bernoulliPositive_14, bernoulliPositive_15, bernoulliPositive_16, bernoulliPositive_17, bernoulliPositive_18, bernoulliPositive_19]

theorem scalarRationalPrefactor_pos : ∀ i : Fin 10, 0 < scalarRationalPrefactor i := by
  decide +kernel

theorem scalarCosecantCoefficient_eq_prefactor (i : Fin 10) :
    scalarCosecantCoefficient (i.val + 1) =
      (scalarRationalPrefactor i : ℝ) * Real.pi ^ (2 * i.val + 1) := by
  fin_cases i <;>
    norm_num [scalarCosecantCoefficient, scalarRationalPrefactor, bernoulli,
      Nat.factorial, div_pow,
      bernoulliPositive_0, bernoulliPositive_2, bernoulliPositive_4, bernoulliPositive_6, bernoulliPositive_8, bernoulliPositive_10, bernoulliPositive_12, bernoulliPositive_14, bernoulliPositive_16, bernoulliPositive_18, bernoulliPositive_20] <;> ring

/-- Rational lower/upper witnesses, with exponent and indexing fixed in the kernel. -/
theorem scalar_coefficient_rational_enclosures : ∀ i : Fin 10,
    (scalarCoefficientNumerator i : ℚ) / 10^12 <
      scalarRationalPrefactor i * (314159265358979323846 / 10^20 : ℚ) ^ (2 * i.val + 1) ∧
    scalarRationalPrefactor i * (314159265358979323847 / 10^20 : ℚ) ^ (2 * i.val + 1) <
      ((scalarCoefficientNumerator i : ℚ) + 1) / 10^12 := by
  decide +kernel

/-- Table J.1's strict intervals, for the actual Bernoulli formula in (I.1). -/
theorem scalar_coefficient_enclosures (i : Fin 10) :
    (scalarCoefficientNumerator i : ℝ) / scalarCoefficientScale <
      scalarCosecantCoefficient (i.val + 1) ∧
    scalarCosecantCoefficient (i.val + 1) <
      ((scalarCoefficientNumerator i : ℝ) + 1) / scalarCoefficientScale := by
  obtain ⟨hl, hu⟩ := scalar_coefficient_rational_enclosures i
  have hl' : (scalarCoefficientNumerator i : ℝ) / 10^12 <
      (scalarRationalPrefactor i : ℝ) *
        (314159265358979323846 / 10^20 : ℝ) ^ (2 * i.val + 1) := by
    have h := (Rat.cast_lt (K := ℝ)).2 hl
    push_cast at h
    exact h
  have hu' : (scalarRationalPrefactor i : ℝ) *
      (314159265358979323847 / 10^20 : ℝ) ^ (2 * i.val + 1) <
      ((scalarCoefficientNumerator i : ℝ) + 1) / 10^12 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hu
    push_cast at h
    exact h
  have hc : (0 : ℝ) ≤ (scalarRationalPrefactor i : ℝ) := by
    exact_mod_cast (scalarRationalPrefactor_pos i).le
  have hpL : (314159265358979323846 / 10^20 : ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_d20]
  have hpU : Real.pi ≤ (314159265358979323847 / 10^20 : ℝ) := by
    linarith [Real.pi_lt_d20]
  rw [scalarCosecantCoefficient_eq_prefactor]
  simp only [scalarCoefficientScale, Nat.cast_pow, Nat.cast_ofNat]
  constructor
  · apply lt_of_lt_of_le hl'
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) hpL (2 * i.val + 1)) hc
  · apply lt_of_le_of_lt _ hu'
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ Real.pi_pos.le hpU (2 * i.val + 1)) hc

end CGLMPBounds.Certificates
