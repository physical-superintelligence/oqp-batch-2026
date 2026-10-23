module

public import CGLMPBounds.Partition.CircularCorrelationShift
public import CGLMPBounds.Partition.CountPolynomial
public import CGLMPBounds.Partition.SourceCountLaw

@[expose] public section


/-! Expectations of the actual circular label correlations, reduced to
actual arc-count atom probabilities and then to the source D.11 law.
No Hardy averaging identity is assumed. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

lemma integral_function_finite_count {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (N : Ω → ℕ) (d : ℕ)
    (hN : Measurable N) (hbound : ∀ ω, N ω ≤ d) (f : ℕ → E) :
    (∫ ω, f (N ω) ∂μ) =
      ∑ h ∈ Finset.range (d + 1), μ.real {ω | N ω = h} • f h := by
  classical
  have hs (h : ℕ) : MeasurableSet {ω | N ω = h} := hN (measurableSet_singleton h)
  have hpoint (ω : Ω) : f (N ω) =
      ∑ h ∈ Finset.range (d + 1), {ω | N ω = h}.indicator (fun _ => f h) ω := by
    simp [Set.indicator_apply, Finset.mem_range, Nat.lt_succ_of_le (hbound ω)]
  calc
    _ = ∫ ω, ∑ h ∈ Finset.range (d + 1),
        {ω | N ω = h}.indicator (fun _ => f h) ω ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ h ∈ Finset.range (d + 1),
        ∫ ω, {ω | N ω = h}.indicator (fun _ => f h) ω ∂μ :=
      integral_finsetSum _ (fun h _ => (integrable_const (f h)).indicator (hs h))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      exact integral_indicator_const _ (hs h)

/-- Actual circular correlations under any finite boundary measure, with
the geometric arc count and its true atom probabilities. -/
theorem circularAssignmentStep_expected_correlation {d r : ℕ} (hd : 0 < d)
    (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] (V : Fin d → Circulation.Mat r)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    (∫ T, ∑ a : Fin d,
      Circulation.corr (circularAssignmentStep hd V a T s)
        (circularAssignmentStep hd V a T t) ∂μ) =
      ∑ h ∈ Finset.range (d + 1),
        (μ.real {T | boundaryArcCount d s (t - s) T = h} : ℂ) *
          ∑ a : Fin d, Circulation.corr (V a) (sourceCyclicExtension hd V (a.val + h)) := by
  calc
    _ = ∫ T, ∑ a : Fin d, Circulation.corr (V a)
        (sourceCyclicExtension hd V (a.val + boundaryArcCount d s (t - s) T)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun T =>
        circularAssignmentStep_correlation_sum hd V T hs hst ht)
    _ = _ := by
      simpa only [Complex.real_smul] using
        integral_function_finite_count μ (boundaryArcCount d s (t - s)) d
          (measurable_boundaryArcCount d s (t - s)) (boundaryArcCount_le d s (t - s))
          (fun h => ∑ a : Fin d,
            Circulation.corr (V a) (sourceCyclicExtension hd V (a.val + h)))

/-- The same genuine expectation for the literal tilted source measure,
using the independently derived D.11 count law. -/
theorem sourcePartition_expected_correlation {d r : ℕ} (hd : 2 ≤ d)
    (V : Fin d → Circulation.Mat r)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    (∫ T, ∑ a : Fin d,
      Circulation.corr (circularAssignmentStep (by omega : 0 < d) V a T s)
        (circularAssignmentStep (by omega : 0 < d) V a T t) ∂sourcePartitionMeasure d) =
      ∑ h ∈ Finset.range (d + 1),
        ((scalarBinomialWeight d h (t - s) + partitionPotential (t - s) / d *
          iteratedDeriv 2 (scalarBinomialWeight d h) (t - s) : ℝ) : ℂ) *
          ∑ a : Fin d, Circulation.corr (V a)
            (sourceCyclicExtension (by omega : 0 < d) V (a.val + h)) := by
  letI : IsProbabilityMeasure (sourcePartitionMeasure d) :=
    sourcePartitionMeasure_isProbabilityMeasure d (by omega)
  have hx : t - s ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  rw [circularAssignmentStep_expected_correlation (by omega : 0 < d)
    (sourcePartitionMeasure d) V hs hst ht]
  simp_rw [sourcePartitionMeasure_count_law d _ hd s (t - s) hx]

end
end CGLMPBounds.Partition
