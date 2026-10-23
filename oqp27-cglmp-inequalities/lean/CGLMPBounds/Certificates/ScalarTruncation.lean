module

public import CGLMPBounds.Defs.ScalarSeries
public import CGLMPBounds.Certificates.ScalarCoefficientBound
public import CGLMPBounds.Certificates.ScalarCoefficientIntervals
public import CGLMPBounds.Certificates.ScalarTailBasic
public import CGLMPBounds.Certificates.ScalarTailGeometric

@[expose] public section


/-!
# The actual uniform truncation estimate (J.3)

All coefficient bounds are proved from the printed Bernoulli formula; the
series is proved absolutely summable before splitting off the ten terms.
The identification of the source series with the preceding integral formulas
and its finite rational-polynomial reconstruction are separate obligations.
-/

namespace CGLMPBounds.Certificates

theorem scalarSeriesTerm_norm_le (i : ℕ) {θ y : ℝ} (hθ : 0 ≤ θ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ‖scalarSeriesTerm i θ y‖ ≤ scalarGeometricMajorant (i + 1) := by
  have hr := scalarCosecantCoefficient_pos_lt (i + 1) (by omega)
  have hE := scalarE_odd_abs_le (i + 1) (by omega) hθ hy
  have hi : 2 * (i + 1) - 1 = 2 * i + 1 := by omega
  rw [hi] at hE
  rw [scalarSeriesTerm, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hr.1]
  exact mul_le_mul hr.2.le hE (abs_nonneg _) (by positivity)

theorem scalarGeometricMajorant_summable : Summable scalarGeometricMajorant :=
  (summable_nat_add_iff 11).1 scalar_geometric_tail_summable

/-- Absolute convergence of the actual coefficient series throughout the source domain. -/
theorem scalarSeriesTerm_summable {θ y : ℝ} (hθ : 0 ≤ θ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : Summable (fun i => scalarSeriesTerm i θ y) :=
  ((summable_nat_add_iff 1).2 scalarGeometricMajorant_summable).of_norm_bounded
    (fun i => scalarSeriesTerm_norm_le i hθ hy)

theorem scalar_coefficient_rounding_abs_le (i : Fin 10) :
    |scalarCosecantCoefficient (i.val + 1) -
      (scalarCoefficientNumerator i : ℝ) / scalarCoefficientScale| ≤
        1 / (scalarCoefficientScale : ℝ) := by
  obtain ⟨hl, hu⟩ := scalar_coefficient_enclosures i
  rw [abs_of_nonneg (sub_nonneg.mpr hl.le)]
  have heq : ((scalarCoefficientNumerator i : ℝ) + 1) / scalarCoefficientScale =
      (scalarCoefficientNumerator i : ℝ) / scalarCoefficientScale +
        1 / (scalarCoefficientScale : ℝ) := by ring
  rw [heq] at hu
  linarith

theorem scalar_rounding_sum_abs_le {θ y : ℝ} (hθ : 0 ≤ θ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |(∑ i : Fin 10, scalarSeriesTerm i.val θ y) - scalarTen θ y| ≤
      (1550 : ℝ) / scalarCoefficientScale := by
  rw [scalarTen, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 10, |scalarSeriesTerm i.val θ y -
        ((scalarCoefficientNumerator i : ℝ) / scalarCoefficientScale) *
          scalarE (2 * i.val + 1) θ y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 10,
        (1 + 4 * (((i.val + 1 : ℕ) : ℝ) ^ 2)) / scalarCoefficientScale := by
      apply Finset.sum_le_sum
      intro i _
      rw [scalarSeriesTerm, ← sub_mul, abs_mul]
      have hE := scalarE_odd_abs_le (i.val + 1) (by omega) hθ hy
      have hi : 2 * (i.val + 1) - 1 = 2 * i.val + 1 := by omega
      rw [hi] at hE
      have h := mul_le_mul (scalar_coefficient_rounding_abs_le i) hE
        (abs_nonneg _) (by positivity : 0 ≤ 1 / (scalarCoefficientScale : ℝ))
      simpa only [one_div_mul_eq_div] using h
    _ = (1550 : ℝ) / scalarCoefficientScale := by
      rw [← Finset.sum_div, scalar_rounding_weight_sum]

theorem scalar_omitted_tail_abs_le {θ y : ℝ} (hθ : 0 ≤ θ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |∑' i : ℕ, scalarSeriesTerm (i + 10) θ y| ≤
      ∑' i : ℕ, scalarGeometricMajorant (i + 11) := by
  have h := tsum_of_norm_bounded scalar_geometric_tail_summable.hasSum
    (fun i => scalarSeriesTerm_norm_le (i + 10) hθ hy)
  simpa only [Real.norm_eq_abs, Nat.add_assoc] using h

/-- The uniform error bound in (J.3), for the source's actual infinite series. -/
theorem scalar_truncation_error_le {θ y : ℝ} (hθ : 0 ≤ θ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |scalarInfinite θ y - scalarTen θ y| ≤ scalarTruncationErrorBudget := by
  have hs := scalarSeriesTerm_summable hθ hy
  have hsplit := hs.sum_add_tsum_nat_add 10
  rw [← Fin.sum_univ_eq_sum_range (fun i => scalarSeriesTerm i θ y)] at hsplit
  have heq : scalarInfinite θ y - scalarTen θ y =
      ((∑ i : Fin 10, scalarSeriesTerm i.val θ y) - scalarTen θ y) +
        ∑' i : ℕ, scalarSeriesTerm (i + 10) θ y := by
    unfold scalarInfinite
    rw [← hsplit]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans
    (by
      simpa only [scalarTruncationErrorBudget, scalarCoefficientScale,
        Nat.cast_pow, Nat.cast_ofNat] using
        add_le_add (scalar_rounding_sum_abs_le hθ hy) (scalar_omitted_tail_abs_le hθ hy))

theorem scalar_truncation_error_lt {θ y : ℝ} (hθ : 0 ≤ θ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |scalarInfinite θ y - scalarTen θ y| < (9 : ℝ) / 40000 :=
  lt_of_le_of_lt (scalar_truncation_error_le hθ hy) scalarTruncationErrorBudget_lt

end CGLMPBounds.Certificates
