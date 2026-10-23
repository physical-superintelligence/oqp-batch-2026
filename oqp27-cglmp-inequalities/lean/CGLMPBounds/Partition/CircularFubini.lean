module

public import CGLMPBounds.Partition.CircularPairDomination
public import CGLMPBounds.Partition.CircularScalarBaseline
public import CGLMPBounds.Partition.CircularPairExpectation

@[expose] public section


/-! Actual random-boundary Fubini for D.3. The full scalar-subtracted
pair function is absolutely integrable before exchanging integrals.
The result still displays the true arc-count probabilities. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix
noncomputable section

theorem circularPartitionHardyAverage_integrable {d r : ℕ}
    (hd : 0 < d) (hr : 0 < r) (V : Fin d → Circulation.Mat r)
    (hV : ∀ j, (V j)ᴴ * V j = 1)
    (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] :
    Integrable (circularPartitionHardyAverage hd V) μ := by
  have hi (a : Fin d) : Integrable (fun T =>
      matrixNegativeFourierEnergy (circularAssignmentBranch hd V a T) -
        sourceFourthRootHardyConstant) μ := by
    have hp := (circularStepPair_integrable_prod hd hr V hV a μ).integral_prod_left
    apply (hp.const_mul (1 / 2 : ℝ)).congr
    exact Filter.Eventually.of_forall (fun T =>
      (circularAssignmentBranch_hardyGap_eq_triangle hd hr V hV a T).symm)
  exact (integrable_finset_sum _ (fun a _ => hi a)).const_mul (1 / (d : ℝ))

/-- Literal D.3 double expectation, with no Fubini hypothesis in the
statement: absolute integrability has been established separately. -/
theorem averagedCircularHardyForm_eq_expected_pair_integral {d r : ℕ}
    (hd : 0 < d) (hr : 0 < r) (V : Fin d → Circulation.Mat r)
    (hV : ∀ j, (V j)ᴴ * V j = 1)
    (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] :
    averagedCircularHardyForm hd μ V =
      (1 / (2 * (d : ℝ))) * (∫ p : ℝ × ℝ,
        ∫ T, ∑ a : Fin d,
          (stepPairIntegrand (circularAssignmentStep hd V a T) p -
            stepPairIntegrand (circularAssignmentStep hd
              (fun _ => (1 : Circulation.Mat r)) a T) p) ∂μ
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  let ν : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))
  let H : (Fin d → ℝ) → ℝ × ℝ → ℝ := fun T p => ∑ a : Fin d,
    (stepPairIntegrand (circularAssignmentStep hd V a T) p -
      stepPairIntegrand (circularAssignmentStep hd (fun _ => (1 : Circulation.Mat r)) a T) p)
  have hH : Integrable (Function.uncurry H) (μ.prod ν) := by
    exact integrable_finset_sum _ (fun a _ =>
      (circularStepPair_integrable_prod hd hr V hV a μ).sub
        (circularStepPair_integrable_prod hd hr (fun _ => (1 : Circulation.Mat r))
          (fun _ => by simp) a μ))
  have hi (T : Fin d → ℝ) (a : Fin d) :
      Integrable (fun p => stepPairIntegrand (circularAssignmentStep hd V a T) p -
        stepPairIntegrand (circularAssignmentStep hd (fun _ => (1 : Circulation.Mat r)) a T) p) ν :=
    (circularAssignmentStep_pair_integrable hd hr V hV a T).sub
      (circularAssignmentStep_pair_integrable hd hr (fun _ => (1 : Circulation.Mat r))
        (fun _ => by simp) a T)
  have he (T : Fin d → ℝ) : circularPartitionHardyAverage hd V T =
      (1 / (2 * (d : ℝ))) * ∫ p, H T p ∂ν := by
    dsimp only [H]
    rw [integral_finset_sum _ (fun a _ => hi T a)]
    have hs (a : Fin d) :
        (∫ p, (stepPairIntegrand (circularAssignmentStep hd V a T) p -
          stepPairIntegrand (circularAssignmentStep hd
            (fun _ => (1 : Circulation.Mat r)) a T) p) ∂ν) =
          ∫ p, stepPairIntegrand (circularAssignmentStep hd V a T) p ∂ν := by
      calc
        _ = (∫ p, stepPairIntegrand (circularAssignmentStep hd V a T) p ∂ν) -
            ∫ p, stepPairIntegrand (circularAssignmentStep hd
              (fun _ => (1 : Circulation.Mat r)) a T) p ∂ν :=
          integral_sub (circularAssignmentStep_pair_integrable hd hr V hV a T)
            (circularAssignmentStep_pair_integrable hd hr
              (fun _ => (1 : Circulation.Mat r)) (fun _ => by simp) a T)
        _ = _ := by
          rw [show (∫ p, stepPairIntegrand (circularAssignmentStep hd
            (fun _ => (1 : Circulation.Mat r)) a T) p ∂ν) = 0 from
              circular_identity_assignment_pair_integral_zero hd hr a T, sub_zero]
    simp_rw [hs]
    unfold circularPartitionHardyAverage
    simp_rw [circularAssignmentBranch_hardyGap_eq_triangle hd hr V hV]
    rw [← Finset.mul_sum]
    ring
  unfold averagedCircularHardyForm
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const_mul,
    integral_integral_swap hH]

/-- The true count probabilities appear after the justified interchange.
No source count law or coefficient identity is inserted into a definition. -/
theorem averagedCircularHardyForm_eq_count_pair_integral {d r : ℕ}
    (hd : 0 < d) (hr : 0 < r) (V : Fin d → Circulation.Mat r)
    (hV : ∀ j, (V j)ᴴ * V j = 1)
    (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] :
    averagedCircularHardyForm hd μ V =
      (1 / (2 * (d : ℝ))) * (∫ p : ℝ × ℝ,
        if p.1 < p.2 then scalarEdgeForm (fun h =>
          scalarSecant (p.2 - p.1) * μ.real
            {T | boundaryArcCount d p.1 (p.2 - p.1) T = h} +
          scalarSecant (1 - p.2 + p.1) * μ.real
            {T | boundaryArcCount d p.1 (p.2 - p.1) T = d - h}) V
        else 0
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  rw [averagedCircularHardyForm_eq_expected_pair_integral hd hr V hV μ]
  congr 1
  apply integral_congr_ae
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  intro p hp
  dsimp only
  by_cases hst : p.1 < p.2
  · rw [if_pos hst]
    exact circularStepPair_expected_sub_scalar hd hr μ V hV hp.1.1.le hst hp.2.2.le
  · simp [stepPairIntegrand, hst]

end
end CGLMPBounds.Partition
