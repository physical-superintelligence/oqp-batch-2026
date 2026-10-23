module

public import CGLMPBounds.Defs.ScalarSeries
public import CGLMPBounds.Certificates.ScalarTailBasic

@[expose] public section


/-!
# The ten-term approximation and the cleared numerator

This module connects the rational finite approximation to the source-factored
integer polynomial. No positivity certificate is assumed by these identities.
-/

namespace CGLMPBounds.Certificates

theorem scalarD_pos (k : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) : 0 < scalarD k θ := by
  apply Finset.prod_pos
  intro j _
  positivity

theorem scalarDstar_pos {θ : ℝ} (hθ : 0 ≤ θ) : 0 < scalarDstar θ :=
  scalarD_pos 19 hθ

theorem scalarD_succ (k : ℕ) (θ : ℝ) :
    scalarD (k + 1) θ = scalarD k θ * (1 + ((k : ℝ) + 2) * θ) := by
  simp [scalarD, Finset.prod_range_succ]

theorem scalarQ_eq_div (k : ℕ) (θ y : ℝ) :
    scalarQ k θ y = scalarP k θ y / scalarD k θ := by
  unfold scalarQ scalarRatio scalarP scalarD
  rw [Finset.prod_div_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  push_cast
  ring

/-- Clearing the source denominator, with every positive theta allowed. -/
theorem scalarE_eq_B_div (k : ℕ) {θ : ℝ} (hθ : 0 < θ) (y : ℝ) :
    scalarE k θ y = scalarB k θ y / (θ * scalarD k θ) := by
  cases k with
  | zero =>
    norm_num [scalarE, hθ.ne', scalarQ, scalarB, scalarP, scalarD]
  | succ k =>
    rw [scalarE, if_neg hθ.ne']
    simp only [scalarQ_eq_div, Nat.add_sub_cancel]
    unfold scalarB
    rw [scalarD_succ]
    have hd := (scalarD_pos k hθ.le).ne'
    have hf : 1 + ((k : ℝ) + 2) * θ ≠ 0 := by positivity
    push_cast
    field_simp [hθ.ne', hd, hf]
    <;> ring

theorem scalarDstar_factor (k : ℕ) (hk : k ≤ 19) (θ : ℝ) :
    scalarDstar θ = scalarD k θ * scalarDquotient k θ := by
  unfold scalarDstar scalarD scalarDquotient
  have hlen : k + (19 - k) = 19 := Nat.add_sub_of_le hk
  conv_lhs => rw [← hlen, Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  push_cast
  ring

/-- The finite ten-term function is precisely N/(Q D_*), including theta=0. -/
theorem scalarTen_eq_numerator {θ : ℝ} (hθ : 0 ≤ θ) (y : ℝ) :
    scalarTen θ y = scalarNumerator θ y /
      ((scalarCoefficientScale : ℝ) * scalarDstar θ) := by
  by_cases hz : θ = 0
  · subst θ
    simp [scalarTen, scalarE, scalarNumerator]
  have hpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hz)
  have hQ : (scalarCoefficientScale : ℝ) ≠ 0 := by norm_num [scalarCoefficientScale]
  have hD := (scalarDstar_pos hθ).ne'
  apply (eq_div_iff (mul_ne_zero hQ hD)).2
  unfold scalarTen scalarNumerator
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarE_eq_B_div _ hpos, scalarDstar_factor (2 * i.val + 1) (by omega)]
  have hk := (scalarD_pos (2 * i.val + 1) hθ).ne'
  field_simp [hQ, hk, hz]
  <;> ring

end CGLMPBounds.Certificates
