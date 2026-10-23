module

public import CGLMPBounds.Defs.PartitionHardy
public import Mathlib.NumberTheory.ZetaValues

@[expose] public section


/-! The scalar-cut constant in D.2: the actual Catalan expression equals
the positive reciprocal-square series printed after D.3. This is derived
from Mathlib's Basel sum and honest even/odd decompositions. -/

namespace CGLMPBounds.Partition
noncomputable section

private lemma reciprocal_arithmetic_square_summable (k b : ℕ) (hk : 0 < k) :
    Summable (fun n : ℕ => (1 : ℝ) / ((k : ℝ) * n + b) ^ 2) := by
  have hi : Function.Injective (fun n : ℕ => k * n + b) := by
    intro m n h
    exact Nat.eq_of_mul_eq_mul_left hk (Nat.add_right_cancel h)
  have h := hasSum_zeta_two.summable.comp_injective hi
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul] using h

lemma odd_reciprocal_square_tsum :
    (∑' n : ℕ, (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 2) = Real.pi ^ 2 / 8 := by
  have he := hasSum_zeta_two.summable.comp_injective
    (show Function.Injective (fun n : ℕ => 2 * n) by
      intro m n h
      change 2 * m = 2 * n at h
      omega)
  have ho := hasSum_zeta_two.summable.comp_injective
    (show Function.Injective (fun n : ℕ => 2 * n + 1) by
      intro m n h
      change 2 * m + 1 = 2 * n + 1 at h
      omega)
  have hsplit := tsum_even_add_odd (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) he ho
  have heval : (∑' n : ℕ, (1 : ℝ) / ((2 * n : ℕ) : ℝ) ^ 2) =
      (1 / 4 : ℝ) * (Real.pi ^ 2 / 6) := by
    calc
      _ = ∑' n : ℕ, (1 / 4 : ℝ) * ((1 : ℝ) / (n : ℝ) ^ 2) := by
        apply tsum_congr
        intro n
        push_cast
        rw [mul_pow, div_mul_eq_div_div]
        ring
      _ = _ := by rw [tsum_mul_left, hasSum_zeta_two.tsum_eq]
  rw [heval, hasSum_zeta_two.tsum_eq] at hsplit
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hsplit
  linarith

theorem sourceCatalanConstant_summable :
    Summable (fun n : ℕ => (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2) := by
  have ho := reciprocal_arithmetic_square_summable 2 1 (by omega)
  apply ho.of_norm_bounded
  intro n
  have hp : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
  simp [Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg hp]

-- Separate the two convergent residue identities so the final scalar algebra
-- does not inline both long even/odd decompositions into one proof term.
set_option maxHeartbeats 800000 in
private lemma odd_reciprocal_subsequence_summable (b : ℕ) :
    Summable (fun n : ℕ => (1 : ℝ) / (2 * ((2 * n + b : ℕ) : ℝ) + 1) ^ 2) := by
  have he (n : ℕ) : 2 * ((2 * n + b : ℕ) : ℝ) + 1 =
      4 * (n : ℝ) + ((2 * b + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  simpa only [he, Nat.cast_ofNat] using reciprocal_arithmetic_square_summable 4 (2 * b + 1) (by omega)

set_option maxHeartbeats 800000 in
private lemma reciprocal_residue_sum :
    (∑' n : ℕ, (1 : ℝ) / (4 * (n : ℝ) + 1) ^ 2) +
      (∑' n : ℕ, (1 : ℝ) / (4 * (n : ℝ) + 3) ^ 2) = Real.pi ^ 2 / 8 := by
  have hoe : Summable (fun n : ℕ => (1 : ℝ) / (2 * ((2 * n : ℕ) : ℝ) + 1) ^ 2) := by
    simpa only [Nat.add_zero] using odd_reciprocal_subsequence_summable 0
  have hoo := odd_reciprocal_subsequence_summable 1
  have hsplit := tsum_even_add_odd
    (f := fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 2) hoe hoo
  have he (n : ℕ) : 2 * ((2 * n : ℕ) : ℝ) + 1 = 4 * (n : ℝ) + 1 := by
    push_cast
    ring
  have hodd (n : ℕ) : 2 * ((2 * n + 1 : ℕ) : ℝ) + 1 = 4 * (n : ℝ) + 3 := by
    push_cast
    ring
  simpa only [he, hodd, odd_reciprocal_square_tsum] using hsplit

set_option maxHeartbeats 800000 in
private lemma sourceCatalanConstant_residue_difference :
    (∑' n : ℕ, (1 : ℝ) / (4 * (n : ℝ) + 1) ^ 2) -
      (∑' n : ℕ, (1 : ℝ) / (4 * (n : ℝ) + 3) ^ 2) = sourceCatalanConstant := by
  let A := ∑' n : ℕ, (1 : ℝ) / (4 * (n : ℝ) + 1) ^ 2
  let B := ∑' n : ℕ, (1 : ℝ) / (4 * (n : ℝ) + 3) ^ 2
  have hce := sourceCatalanConstant_summable.comp_injective
    (show Function.Injective (fun n : ℕ => 2 * n) by
      intro m n h
      change 2 * m = 2 * n at h
      omega)
  have hco := sourceCatalanConstant_summable.comp_injective
    (show Function.Injective (fun n : ℕ => 2 * n + 1) by
      intro m n h
      change 2 * m + 1 = 2 * n + 1 at h
      omega)
  have hcatsplit := tsum_even_add_odd
    (f := fun n : ℕ => (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2) hce hco
  have hcA : (∑' n : ℕ, (-1 : ℝ) ^ (2 * n) /
      (2 * ((2 * n : ℕ) : ℝ) + 1) ^ 2) = A := by
    apply tsum_congr
    intro n
    norm_num [pow_mul, pow_add] <;> push_cast <;> ring
  have hcB : (∑' n : ℕ, (-1 : ℝ) ^ (2 * n + 1) /
      (2 * ((2 * n + 1 : ℕ) : ℝ) + 1) ^ 2) = -B := by
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    norm_num [pow_mul, pow_add] <;> push_cast <;> ring
  rw [hcA, hcB] at hcatsplit
  change A + -B = sourceCatalanConstant at hcatsplit
  simpa only [sub_eq_add_neg] using hcatsplit

set_option maxHeartbeats 800000 in
theorem sourceFourthRootHardyConstant_eq_positive_series :
    sourceFourthRootHardyConstant = (8 / Real.pi ^ 2) *
      ∑' n : ℕ, (1 : ℝ) / (4 * (n : ℝ) + 3) ^ 2 := by
  let A := ∑' n : ℕ, (1 : ℝ) / (4 * (n : ℝ) + 1) ^ 2
  let B := ∑' n : ℕ, (1 : ℝ) / (4 * (n : ℝ) + 3) ^ 2
  have hsplit : A + B = Real.pi ^ 2 / 8 := reciprocal_residue_sum
  have hcatsplit : A - B = sourceCatalanConstant := sourceCatalanConstant_residue_difference
  change 1 / 2 - 4 * sourceCatalanConstant / Real.pi ^ 2 = (8 / Real.pi ^ 2) * B
  have hB : B = Real.pi ^ 2 / 16 - sourceCatalanConstant / 2 := by
    linarith [hsplit, hcatsplit]
  rw [hB]
  field_simp [Real.pi_ne_zero]
  <;> ring

end
end CGLMPBounds.Partition
