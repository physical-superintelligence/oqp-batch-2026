module

public import CGLMPBounds.Certificates.ScalarBetaSeries
public import CGLMPBounds.Certificates.ScalarCorrection
public import CGLMPBounds.Certificates.ScalarNormalization

@[expose] public section


/-!
# The integral-to-series identity (I.2) and full normalization (J.1)

Integral coefficients retain their literal D.6 definitions.
-/

namespace CGLMPBounds.Certificates
noncomputable section

theorem scalarBetaPole_intervalIntegrable (d h : ℕ) (hh : h < d) :
    IntervalIntegrable (fun x => scalarBinomialWeight d h x * (1 / (1 - x)))
      MeasureTheory.volume 0 1 := by
  let q := d - h - 1
  have hq : q + 1 = d - h := by dsimp [q]; omega
  have hc : Continuous (fun x : ℝ => (d.choose h : ℝ) * x ^ h * (1 - x) ^ q) := by
    fun_prop
  apply (hc.intervalIntegrable 0 1).congr_uIoo
  intro x hx
  have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hx
  have hx1 : 1 - x ≠ 0 := by linarith [hx'.2]
  unfold scalarBinomialWeight
  dsimp only
  rw [← hq, pow_succ]
  field_simp [hx1]
  <;> ring

lemma scalarSecant_eq_pole_add_series {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    scalarSecant x = (2 / Real.pi) * (1 / (1 - x)) + scalarRegularSeries (1 - x) := by
  rw [scalarRegularSeries_eq (scalar_reflect_mem_Icc ⟨hx.1.le, hx.2.le⟩),
    scalarSecant_reflected]
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  field_simp [Real.pi_ne_zero, hx1]
  <;> ring

theorem scalarBetaSecant_eq (d h : ℕ) (hh : h < d) :
    scalarBetaTransform d h scalarSecant =
      (2 / Real.pi) * scalarBetaTransform d h (fun x => 1 / (1 - x)) +
        scalarBetaTransform d h (fun x => scalarRegularSeries (1 - x)) := by
  have hp := (scalarBetaPole_intervalIntegrable d h hh).const_mul (2 / Real.pi)
  have hr := scalarBetaRegular_intervalIntegrable d h
  unfold scalarBetaTransform
  have he : (∫ x in (0 : ℝ)..1, scalarBinomialWeight d h x * scalarSecant x) =
      ∫ x in (0 : ℝ)..1,
        (2 / Real.pi) * (scalarBinomialWeight d h x * (1 / (1 - x))) +
          scalarBinomialWeight d h x * scalarRegularSeries (1 - x) := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro x hx
    dsimp only
    rw [scalarSecant_eq_pole_add_series hx]
    ring
  rw [he, intervalIntegral.integral_add hp hr, intervalIntegral.integral_const_mul]
  ring

theorem scalarBetaCorrection_eq (d h : ℕ) :
    scalarBetaTransform d h scalarCorrectionB =
      -(1 : ℝ) / 2 * scalarBetaTransform d h (fun x => scalarPhiSeries 2 (1 - x)) := by
  unfold scalarBetaTransform
  have he : (∫ x in (0 : ℝ)..1, scalarBinomialWeight d h x * scalarCorrectionB x) =
      ∫ x in (0 : ℝ)..1,
        (-(1 : ℝ) / 2) * (scalarBinomialWeight d h x * scalarPhiSeries 2 (1 - x)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro x hx
    dsimp only
    rw [scalarCorrectionB_eq_series hx]
    ring
  rw [he, intervalIntegral.integral_const_mul]
  ring

lemma scalar_separation_mem (d h : ℕ) (hh0 : 0 < h) (hhd : h < d) :
    (h : ℝ) / d ∈ Set.Ioo (0 : ℝ) 1 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  constructor
  · exact div_pos (by exact_mod_cast hh0) hd
  · exact (div_lt_one hd).2 (by exact_mod_cast hhd)

/-- Remove the source pole before evaluating the convergent regular part. -/
theorem scalarIntegralError_eq_regular (d h : ℕ) (hh0 : 0 < h) (hhd : h < d) :
    scalarIntegralError d h = scalarRegularSeries (1 - (h : ℝ) / d) -
      scalarBetaTransform d h (fun x => scalarRegularSeries (1 - x)) +
        (1 / (2 * (d : ℝ))) * scalarBetaTransform d h (fun x => scalarPhiSeries 2 (1 - x)) := by
  unfold scalarIntegralError
  rw [scalarSecant_eq_pole_add_series (scalar_separation_mem d h hh0 hhd),
    scalarBetaSecant_eq d h hhd, scalarBetaCorrection_eq,
    scalarBetaTransform_pole d h hhd]
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hdh : (d : ℝ) - h ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (by exact_mod_cast hhd))
  have hfrac : 1 - (h : ℝ) / d ≠ 0 := by
    have hsep := scalar_separation_mem d h hh0 hhd
    linarith [hsep.2]
  field_simp [Real.pi_ne_zero, hd, hdh, hfrac]
  <;> ring

/-- The full I.2 assertion as a convergent series for the integral-defined error. -/
theorem scalarIntegralError_hasSum (d h : ℕ) (hh0 : 0 < h) (hhd : h < d) :
    HasSum (fun i : ℕ => scalarCosecantCoefficient (i + 1) * scalarErrorBracket d h (2 * i + 1))
      (scalarIntegralError d h) := by
  have hy := scalarPhi_reflection_mem (scalar_separation_mem d h hh0 hhd)
  have hp := (scalarRegularTerm_summable ⟨hy.1.le, hy.2.le⟩).hasSum
  have hr := scalarBetaRegular_hasSum d h hhd.le
  have hc := (scalarBetaPhi_two_hasSum d h hhd.le).mul_left (1 / (2 * (d : ℝ)))
  have hs := (hp.sub hr).add hc
  change HasSum _ (scalarRegularSeries (1 - (h : ℝ) / d) -
    scalarBetaTransform d h (fun x => scalarRegularSeries (1 - x)) +
      (1 / (2 * (d : ℝ))) * scalarBetaTransform d h (fun x => scalarPhiSeries 2 (1 - x))) at hs
  rw [← scalarIntegralError_eq_regular d h hh0 hhd] at hs
  convert hs using 1
  ext i
  unfold scalarRegularTerm scalarErrorBracket
  rw [show 2 * i + 1 - 1 = 2 * i by omega]
  push_cast
  ring

/-- Integral D.6 equals the explicit source I.2 series; no analytic equality is
supplied as a hypothesis. -/
theorem scalarIntegralError_eq_seriesError (d h : ℕ) (hh0 : 0 < h) (hhd : h < d) :
    scalarIntegralError d h = scalarSeriesError d h :=
  (scalarIntegralError_hasSum d h hh0 hhd).tsum_eq.symm

/-- Full J.1, now with the actual integral-defined error on the right. -/
theorem scalarInfinite_reciprocal_eq_integralError (d h : ℕ) (hh0 : 0 < h) (hhd : h < d) :
    scalarInfinite (1 / d) (1 - (h : ℝ) / d) = ((d : ℝ) + 1) * scalarIntegralError d h := by
  rw [scalarInfinite_reciprocal_eq_seriesError d h (by omega),
    scalarIntegralError_eq_seriesError d h hh0 hhd]

end
end CGLMPBounds.Certificates
