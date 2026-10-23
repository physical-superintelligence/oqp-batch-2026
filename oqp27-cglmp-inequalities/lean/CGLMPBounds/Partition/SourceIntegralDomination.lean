module

public import CGLMPBounds.Partition.SourceCountLaw
public import CGLMPBounds.Partition.MixtureIntegrals

@[expose] public section


/-! Domination by the literal D.10 source density for actual integrable
nonnegative observables. The density bound is derived from the source
Fourier coefficients. Applying this to Hardy forms still requires their
genuine measurability, integrability, and C.6 nonnegativity. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

theorem sourcePartitionDensity_norm_le (d : ℕ) (T : Fin d → ℝ) :
    ‖sourcePartitionDensity d T‖ ≤
      (3 / 2 - Real.pi / 4) + (Real.pi / 4 - 1 / 2) * d := by
  have hc : 0 ≤ (3 / 2 - Real.pi / 4 : ℝ) := by linarith [Real.pi_lt_four]
  have h := norm_fourierMixtureDensity_le d partitionFourierCoefficient
    (fun n => (partitionFourierCoefficient_pos n).le)
    partitionFourierCoefficient_summable T
  simpa only [sourcePartitionDensity, sourcePartitionResidual,
    partitionFourierCoefficient_tsum, Real.norm_of_nonneg hc] using h

theorem integrable_sourcePartitionDensity_mul (d : ℕ)
    (F : (Fin d → ℝ) → ℝ) (hF : Integrable F (boundaryProductMeasure d)) :
    Integrable (fun T => sourcePartitionDensity d T * F T) (boundaryProductMeasure d) := by
  have hD : AEStronglyMeasurable (sourcePartitionDensity d) (boundaryProductMeasure d) :=
    (continuous_fourierMixtureDensity d partitionFourierCoefficient
      (fun n => (partitionFourierCoefficient_pos n).le)
      partitionFourierCoefficient_summable).aestronglyMeasurable
  exact hF.bdd_mul hD (Filter.Eventually.of_forall (sourcePartitionDensity_norm_le d))

/-- Every genuinely integrable nonnegative observable is dominated by
the literal source measure with the exact manuscript constant c*. -/
theorem sourcePartition_integral_ge_residual (d : ℕ)
    (F : (Fin d → ℝ) → ℝ) (hF : Integrable F (boundaryProductMeasure d))
    (hF0 : ∀ᵐ T ∂boundaryProductMeasure d, 0 ≤ F T) :
    (3 / 2 - Real.pi / 4) * (∫ T, F T ∂boundaryProductMeasure d) ≤
      ∫ T, F T ∂sourcePartitionMeasure d := by
  have he := integral_fourierMixtureMeasure d partitionFourierCoefficient
    (fun n => (partitionFourierCoefficient_pos n).le)
    partitionFourierCoefficient_summable sourcePartitionCoefficientMass_lt_one.le F
  change _ ≤ ∫ T, F T ∂fourierMixtureMeasure d partitionFourierCoefficient
  rw [he, ← integral_const_mul]
  apply integral_mono_ae (hF.const_mul _) (integrable_sourcePartitionDensity_mul d F hF)
  filter_upwards [hF0] with T hT
  exact mul_le_mul_of_nonneg_right (sourcePartitionDensity_lower d T) hT

end
end CGLMPBounds.Partition
