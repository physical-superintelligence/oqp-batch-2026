module

public import CGLMPBounds.Partition.SourceHardyForm
public import CGLMPBounds.Partition.UniformHardyAveraging
public import CGLMPBounds.Circulation.ScalarForm

@[expose] public section


/-!
# Internal D.1 assembly conditional on the actual C.6 nonnegativity input

The C.6 nonnegativity input enters as the premise `hC6`. The file connects it to
the already constructed actual averages and coefficient estimates.
-/

namespace CGLMPBounds.Partition
open MeasureTheory
open scoped Matrix
noncomputable section

/-- Conditional D.1 with the full positive-partition term retained. -/
theorem scalar_fourth_root_bound_of_C6_input {d r : ℕ} [NeZero r] (hd : 2 ≤ d)
    (V : Fin d → Circulation.Mat r) (hunit : ∀ j, (V j)ᴴ*V j=1)
    (hfour : ∀ j, V j^4=1)
    (hC6 : ∀ᵐ T ∂boundaryProductMeasure d,
      0 ≤ circularPartitionHardyAverage (by omega : 0 < d) V T) :
    0 ≤ scalarEdgeForm (fun h => scalarBetaTransform d h scalarSecant / (2*(d : ℝ)^2)) V ∧
    (3/2-Real.pi/4) *
      scalarEdgeForm (fun h => scalarBetaTransform d h scalarSecant / (2*(d : ℝ)^2)) V +
        scalarForbiddenTotal V / (6*(d : ℝ)^2*((d : ℝ)+1)) ≤
      scalarEdgeForm (fun h => scalarSecant ((h : ℝ)/d) / (2*(d : ℝ)^2)) V := by
  have hd0 : 0 < d := by omega
  have hr : 0 < r := NeZero.pos r
  have hu := uniform_averagedCircularHardyForm_eq_beta hd0 hr V hunit
  have hnon : 0 ≤ averagedCircularHardyForm hd0 (boundaryProductMeasure d) V :=
    integral_nonneg_of_ae hC6
  have hdom := sourcePartition_integral_ge_residual d (circularPartitionHardyAverage hd0 V)
    (circularPartitionHardyAverage_integrable hd0 hr V hunit (boundaryProductMeasure d))
    hC6
  have hc := Circulation.scalarEdgeForm_error_partition_coercivity hd V hunit hfour
  have hs := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ 1/(2*(d : ℝ)^2) by positivity)
  have he := sampledEdgeForm_eq_actualHardyAverage_add_error hd hr V hunit
  refine ⟨by simpa only [hu] using hnon, ?_⟩
  have hn : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hn' : (d : ℝ)+1 ≠ 0 := by positivity
  have hscale : (1/(2*(d : ℝ)^2))*(scalarForbiddenTotal V/(3*((d : ℝ)+1))) =
      scalarForbiddenTotal V/(6*(d : ℝ)^2*((d : ℝ)+1)) := by
    field_simp [hn, hn']
    <;> ring
  change (3/2-Real.pi/4)*averagedCircularHardyForm hd0 (boundaryProductMeasure d) V ≤
    averagedCircularHardyForm hd0 (sourcePartitionMeasure d) V at hdom
  rw [hscale] at hs
  have h := add_le_add hdom hs
  rw [hu, ← he] at h
  exact h

/-- The conditional coercive part used by E.5; the C.6 input remains explicit. -/
theorem scalar_forbidden_lower_of_C6_input {d r : ℕ} [NeZero r] (hd : 2 ≤ d)
    (V : Fin d → Circulation.Mat r) (hunit : ∀ j, (V j)ᴴ*V j=1)
    (hfour : ∀ j, V j^4=1)
    (hC6 : ∀ᵐ T ∂boundaryProductMeasure d,
      0 ≤ circularPartitionHardyAverage (by omega : 0 < d) V T) :
    scalarForbiddenTotal V/(6*(d : ℝ)^2*((d : ℝ)+1)) ≤
      scalarEdgeForm (fun h => scalarSecant ((h : ℝ)/d)/(2*(d : ℝ)^2)) V := by
  obtain ⟨hD, hG⟩ := scalar_fourth_root_bound_of_C6_input hd V hunit hfour hC6
  have hc : (0 : ℝ) ≤ 3/2-Real.pi/4 := by linarith [Real.pi_lt_four]
  linarith [mul_nonneg hc hD]

end
end CGLMPBounds.Partition
