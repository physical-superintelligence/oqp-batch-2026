module

public import CGLMPBounds.Certificates.BetaSeriesAlgebra
public import CGLMPBounds.Certificates.ScalarRegularSeries
public import CGLMPBounds.Certificates.UniformIntervalSeries

@[expose] public section


/-!
# Integration of the convergent scalar series against the beta weight
-/

namespace CGLMPBounds.Certificates
noncomputable section

lemma scalar_reflect_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    1 - x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> linarith [hx.1, hx.2]

lemma scalarRegular_reflected_continuous (i : ℕ) :
    ContinuousOn (fun x : ℝ => scalarRegularTerm i (1 - x)) (Set.Icc (0 : ℝ) 1) := by
  apply Continuous.continuousOn
  unfold scalarRegularTerm
  fun_prop

lemma scalarPhi_reflected_continuous (i m : ℕ) :
    ContinuousOn (fun x : ℝ => scalarPhiTerm i m (1 - x)) (Set.Icc (0 : ℝ) 1) := by
  apply Continuous.continuousOn
  unfold scalarPhiTerm scalarPowerDerivative
  fun_prop

theorem scalarBetaRegular_intervalIntegrable (d h : ℕ) :
    IntervalIntegrable
      (fun x => scalarBinomialWeight d h x * scalarRegularSeries (1 - x))
      MeasureTheory.volume 0 1 := by
  exact uniform_interval_weighted_intervalIntegrable
    (fun i x => scalarRegularTerm i (1 - x)) scalarRegularMajorant
    (scalarBinomialWeight d h) scalarRegular_reflected_continuous
    scalarRegularMajorant_summable
    (fun i x hx => scalarRegularTerm_bound i (scalar_reflect_mem_Icc hx))
    (scalarBinomialWeight_continuous d h).continuousOn

theorem scalarBetaPhi_intervalIntegrable (d h m : ℕ) :
    IntervalIntegrable
      (fun x => scalarBinomialWeight d h x * scalarPhiSeries m (1 - x))
      MeasureTheory.volume 0 1 := by
  exact uniform_interval_weighted_intervalIntegrable
    (fun i x => scalarPhiTerm i m (1 - x)) (scalarPhiMajorant m)
    (scalarBinomialWeight d h) (fun i => scalarPhi_reflected_continuous i m)
    (scalarPhiMajorant_summable m)
    (fun i x hx => scalarPhiTerm_bound i m (scalar_reflect_mem_Icc hx))
    (scalarBinomialWeight_continuous d h).continuousOn

/-- The regularized beta integral is the genuinely convergent moment series. -/
theorem scalarBetaRegular_hasSum (d h : ℕ) (hh : h ≤ d) :
    HasSum (fun i : ℕ => scalarCosecantCoefficient (i + 1) * scalarBetaMoment d h (2 * i + 1))
      (scalarBetaTransform d h (fun x => scalarRegularSeries (1 - x))) := by
  have hsum := uniform_interval_weighted_hasSum
    (fun i x => scalarRegularTerm i (1 - x)) scalarRegularMajorant
    (scalarBinomialWeight d h) (d.choose h : ℝ) scalarRegular_reflected_continuous
    scalarRegularMajorant_summable
    (fun i x hx => scalarRegularTerm_bound i (scalar_reflect_mem_Icc hx))
    (scalarBinomialWeight_continuous d h).continuousOn
    (fun x hx => scalarBinomialWeight_bound d h hx)
  convert hsum.mul_left (d : ℝ) using 1
  · ext i
    change scalarCosecantCoefficient (i + 1) * scalarBetaMoment d h (2 * i + 1) =
      scalarBetaTransform d h (fun x => scalarRegularTerm i (1 - x))
    simp only [scalarRegularTerm]
    rw [scalarBetaTransform_const_mul,
      scalarBetaTransform_power_eq_moment d h (2 * i + 1) hh]
  · rfl

/-- Integration of every derivative series, before specializing to order two. -/
theorem scalarBetaPhi_hasSum (d h m : ℕ) :
    HasSum (fun i : ℕ => scalarBetaTransform d h (fun x => scalarPhiTerm i m (1 - x)))
      (scalarBetaTransform d h (fun x => scalarPhiSeries m (1 - x))) := by
  have hsum := uniform_interval_weighted_hasSum
    (fun i x => scalarPhiTerm i m (1 - x)) (scalarPhiMajorant m)
    (scalarBinomialWeight d h) (d.choose h : ℝ) (fun i => scalarPhi_reflected_continuous i m)
    (scalarPhiMajorant_summable m)
    (fun i x hx => scalarPhiTerm_bound i m (scalar_reflect_mem_Icc hx))
    (scalarBinomialWeight_continuous d h).continuousOn
    (fun x hx => scalarBinomialWeight_bound d h hx)
  exact hsum.mul_left (d : ℝ)

/-- The explicit moment bracket for the integrated second derivative. -/
theorem scalarBetaPhi_two_hasSum (d h : ℕ) (hh : h ≤ d) :
    HasSum (fun i : ℕ => scalarCosecantCoefficient (i + 1) *
      (((2 * i : ℝ) + 1) * ((2 * i : ℝ) + 2) * scalarBetaMoment d h (2 * i) -
        ((2 * i : ℝ) + 2) * ((2 * i : ℝ) + 3) * scalarBetaMoment d h (2 * i + 1)))
      (scalarBetaTransform d h (fun x => scalarPhiSeries 2 (1 - x))) := by
  simpa only [scalarBetaTransform_phiTerm_two d h _ hh] using scalarBetaPhi_hasSum d h 2

end
end CGLMPBounds.Certificates
