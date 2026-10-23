module

public import CGLMPBounds.Partition.SourceHardyAveraging
public import CGLMPBounds.Partition.SourceFormDecomposition
public import CGLMPBounds.Partition.SourceIntegralDomination

@[expose] public section


/-! Literal D.8 decomposition and density representation of the actual
averaged Hardy form. The separate C.6 nonnegativity obligation is not
replaced by a premise or asserted here. -/

namespace CGLMPBounds.Partition
open MeasureTheory
open scoped Matrix
noncomputable section

theorem sourceHardyAverage_density_integrable {d r : ℕ}
    (hd : 0 < d) (hr : 0 < r) (V : Fin d → Circulation.Mat r)
    (hV : ∀ j, (V j)ᴴ * V j = 1) :
    Integrable (fun T => sourcePartitionDensity d T * circularPartitionHardyAverage hd V T)
      (boundaryProductMeasure d) :=
  integrable_sourcePartitionDensity_mul d _
    (circularPartitionHardyAverage_integrable hd hr V hV (boundaryProductMeasure d))

theorem sourceHardyAverage_density_identity {d r : ℕ}
    (hd : 0 < d) (V : Fin d → Circulation.Mat r) :
    averagedCircularHardyForm hd (sourcePartitionMeasure d) V =
      ∫ T, sourcePartitionDensity d T * circularPartitionHardyAverage hd V T
        ∂boundaryProductMeasure d :=
  integral_fourierMixtureMeasure d partitionFourierCoefficient
    (fun n => (partitionFourierCoefficient_pos n).le)
    partitionFourierCoefficient_summable sourcePartitionCoefficientMass_lt_one.le _

/-- D.8 now contains the actual averaged Fourier Hardy gap, with its
literal probability-space definition, not a replacement coefficient form. -/
theorem sampledEdgeForm_eq_actualHardyAverage_add_error {d r : ℕ}
    (hd : 2 ≤ d) (hr : 0 < r) (V : Fin d → Circulation.Mat r)
    (hV : ∀ j, (V j)ᴴ * V j = 1) :
    scalarEdgeForm (fun h => scalarSecant ((h : ℝ) / d) / (2 * (d : ℝ) ^ 2)) V =
      averagedCircularHardyForm (by omega : 0 < d) (sourcePartitionMeasure d) V +
        (1 / (2 * (d : ℝ) ^ 2)) *
          scalarEdgeForm (fun h => scalarIntegralError d h + scalarPartitionCoefficient d h) V := by
  rw [source_averagedCircularHardyForm_eq_coefficients hd hr V hV]
  exact scalarEdgeForm_source_decomposition hd V 0

end
end CGLMPBounds.Partition
