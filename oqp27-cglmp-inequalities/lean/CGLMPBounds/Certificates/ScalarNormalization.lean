module

public import CGLMPBounds.Defs.ScalarBeta

@[expose] public section


/-!
# Algebraic normalization from the Appendix I series to Appendix J

This proves the normalization for the literal (I.2) series. The identity of
that series with the integral coefficient (D.6) remains a separate analytic
obligation; this module does not claim the full J.1 bridge on its own.
-/

namespace CGLMPBounds.Certificates

theorem scalarBetaMoment_eq_Q (d h k : ℕ) (hd : d ≠ 0) :
    scalarBetaMoment d h k = (d : ℝ) / ((d : ℝ) + 1) *
      scalarQ k (1 / d) (1 - (h : ℝ) / d) := by
  unfold scalarBetaMoment scalarQ
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  unfold scalarRatio
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hden : (d : ℝ) + j + 2 ≠ 0 := by positivity
  push_cast
  field_simp [hd0, hden]
  <;> ring

/-- Normalization of every bracket, including all denominator factors. -/
theorem scalarE_reciprocal_eq_bracket (d h k : ℕ) (hd : d ≠ 0) :
    scalarE k (1 / d) (1 - (h : ℝ) / d) =
      ((d : ℝ) + 1) * scalarErrorBracket d h k := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  rw [scalarE, if_neg (one_div_ne_zero hd0)]
  unfold scalarErrorBracket
  rw [scalarBetaMoment_eq_Q d h k hd, scalarBetaMoment_eq_Q d h (k - 1) hd]
  field_simp [hd0, hd1]
  <;> ring

/-- The exact (d+1) factor in J.1 for the explicit I.2 coefficient series. -/
theorem scalarInfinite_reciprocal_eq_seriesError (d h : ℕ) (hd : d ≠ 0) :
    scalarInfinite (1 / d) (1 - (h : ℝ) / d) =
      ((d : ℝ) + 1) * scalarSeriesError d h := by
  unfold scalarInfinite scalarSeriesTerm scalarSeriesError
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  rw [scalarE_reciprocal_eq_bracket d h (2 * i + 1) hd]
  ring

end CGLMPBounds.Certificates
