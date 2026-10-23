module

public import CGLMPBounds.Hardy.PoissonRadialSequence
public import CGLMPBounds.Hardy.ContinuousGrowthL2L1

@[expose] public section


/-! Genuine boundary mean for the literal matrix Hardy potential.
The actual Fourier radial L² limit is passed through the continuous root
potential using the proved finite-measure linear-growth L¹ theorem. -/
namespace CGLMPBounds.Hardy
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem matrixPoisson_boundary_potential_mean {r : ℕ} (hr : 0 < r)
    (B : UnitCircle → Circulation.Mat r) (hB : AEStronglyMeasurable B circleMeasure)
    (hherm : ∀ᵐ t ∂circleMeasure, (B t).IsHermitian)
    (hbound : ∀ᵐ t ∂circleMeasure, ‖B t‖ ≤ 1)
    (hmean : (∫ t, B t ∂circleMeasure)=0) :
    Integrable (fun t => matrixHardyPotential (B t+Complex.I • matrixHilbert B t)) circleMeasure ∧
    (∫ t, matrixHardyPotential (B t+Complex.I • matrixHilbert B t) ∂circleMeasure) =
      hardyStripCenterConstant := by
  have hB2 := circle_bounded_matrix_memLp hB hbound
  let F : ℕ → UnitCircle → Circulation.Mat r :=
    fun n => matrixPoissonRadial B (hardyRadialSequence n)
  let F₀ : UnitCircle → Circulation.Mat r := fun t => B t+Complex.I • matrixHilbert B t
  have hconv := continuousOn_linear_growth_L2_L1 circleMeasure
    {X : Circulation.Mat r | ‖hermitianRealPart X‖ ≤ 1}
    (isClosed_realPart_contractions r) matrixHardyPotential
    (continuousOn_matrixHardyPotential_realPart_contractions r)
    (|hardyStripCenterConstant|+1) (by positivity)
    (fun X hX => matrixHardyPotential_linear_growth hr hX)
    F F₀ (fun n => matrixPoissonRadial_memLp_operator hB2 (hardyRadialSequence_mem n))
    (matrixPoisson_boundary_memLp hB2)
    (fun n => Eventually.of_forall fun t => matrixPoissonRadial_mem_closed_strip B
      hB hherm hbound hmean (hardyRadialSequence_mem n) t)
    (matrixPoisson_boundary_mem_closed_strip hB2 hherm hbound)
    (matrixPoissonRadial_sequence_eLpNorm_tendsto hB2)
  refine ⟨hconv.2.1, ?_⟩
  have hconstant (n : ℕ) :
      (∫ t, matrixHardyPotential (F n t) ∂circleMeasure)=hardyStripCenterConstant :=
    (matrixPoissonRadial_potential_mean hr B hB hherm hbound hmean
      (hardyRadialSequence_mem n)).2
  have hbound' (n : ℕ) :
      |hardyStripCenterConstant-(∫ t, matrixHardyPotential (F₀ t) ∂circleMeasure)| ≤
        ∫ t, |matrixHardyPotential (F n t)-matrixHardyPotential (F₀ t)| ∂circleMeasure := by
    rw [← hconstant n,← integral_sub (hconv.1 n) hconv.2.1]
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (fun t => matrixHardyPotential (F n t)-matrixHardyPotential (F₀ t))
  have hz := ge_of_tendsto' hconv.2.2 hbound'
  have he : hardyStripCenterConstant-(∫ t, matrixHardyPotential (F₀ t) ∂circleMeasure)=0 :=
    abs_nonpos_iff.mp hz
  exact (sub_eq_zero.mp he).symm

end
end CGLMPBounds.Hardy
