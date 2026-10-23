module

public import CGLMPBounds.Partition.SourceCoefficientIntegrability

@[expose] public section


/-! Exact D.7–D.8 scalar coefficient matching from the actual source
probabilities. This does not stand in for the still separate D.2 Hardy-form
and circular-partition identification. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory CGLMPBounds.Certificates
noncomputable section

theorem sourcePartitionCoefficient_eq_beta (d h : ℕ) (hh0 : 0 < h) (hhd : h < d)
    (origin : ℝ) :
    sourcePartitionCoefficient d h origin =
      (scalarBetaTransform d h scalarSecant +
        scalarBetaTransform d h scalarCorrectionB / d - scalarPartitionCoefficient d h) /
          (2 * (d : ℝ) ^ 2) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have h0 := binomial_secant_intervalIntegrable d h hhd
  have h1 := (potential_binomial_correction_intervalIntegrable d h).const_mul (1 / (d : ℝ))
  have hb := binomial_correction_intervalIntegrable d h
  have hs := scalarPartition_weight_intervalIntegrable d h
  have he : (∫ x in (0 : ℝ)..1, scalarSecant x *
      (sourcePartitionMeasure d).real {T | boundaryArcCount d origin x T = h}) =
      ∫ x in (0 : ℝ)..1, scalarBinomialWeight d h x * scalarSecant x +
        (1 / (d : ℝ)) * (partitionPotential x * scalarSecant x *
          iteratedDeriv 2 (scalarBinomialWeight d h) x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
    dsimp only
    rw [sourcePartitionMeasure_count_law d h (by omega) origin x hx']
    ring
  unfold sourcePartitionCoefficient
  rw [he, intervalIntegral.integral_add h0 h1, intervalIntegral.integral_const_mul,
    potential_binomial_second_transfer d h hh0 hhd]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hb hs]
  simp only [scalarBetaTransform, scalarPartitionCoefficient]
  field_simp [hd]
  <;> ring

/-- Exact decomposition of the sampled secant coefficient in D.8. -/
theorem sourcePartitionCoefficient_error_decomposition (d h : ℕ)
    (hh0 : 0 < h) (hhd : h < d) (origin : ℝ) :
    scalarSecant ((h : ℝ) / d) / (2 * (d : ℝ) ^ 2) =
      sourcePartitionCoefficient d h origin +
        (scalarIntegralError d h + scalarPartitionCoefficient d h) / (2 * (d : ℝ) ^ 2) := by
  rw [sourcePartitionCoefficient_eq_beta d h hh0 hhd origin]
  unfold scalarIntegralError
  ring

theorem sourcePartitionCoefficient_origin_independent (d h : ℕ)
    (hh0 : 0 < h) (hhd : h < d) (origin₁ origin₂ : ℝ) :
    sourcePartitionCoefficient d h origin₁ = sourcePartitionCoefficient d h origin₂ := by
  rw [sourcePartitionCoefficient_eq_beta d h hh0 hhd origin₁,
    sourcePartitionCoefficient_eq_beta d h hh0 hhd origin₂]

end
end CGLMPBounds.Partition
