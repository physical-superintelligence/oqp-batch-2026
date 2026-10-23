module

public import CGLMPBounds.Defs.HardyMatrixPotential
public import CGLMPBounds.Hardy.CircleMatrixL2
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

@[expose] public section


/-! Continuity and L² integrability of the actual normalized absolute trace.
The operator-norm calculation is isolated. The public integrability statement
uses ordinary entrywise matrix L²; an actual finite-dimensional linear map
to Euclidean operators transports the bound. -/
namespace CGLMPBounds.Hardy
open MeasureTheory Matrix
noncomputable section
local instance matrixAbsoluteIntegrabilityUnitPeriod : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

section OperatorNorm
open scoped Matrix.Norms.L2Operator MatrixOrder
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

 theorem continuous_normalizedMatrixAbsTrace {r : ℕ} :
    Continuous (normalizedMatrixAbsTrace : Circulation.Mat r → ℝ) := by
  have hc : Continuous (CFC.abs : Circulation.Mat r → Circulation.Mat r) := CFC.continuous_abs
  unfold normalizedMatrixAbsTrace
  fun_prop

theorem normalizedMatrixAbsTrace_operator_bound {r : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : Circulation.Mat r,
      ‖normalizedMatrixAbsTrace X‖ ≤ C*‖Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) X‖ := by
  let tr : Circulation.Mat r →L[ℂ] ℂ := (Matrix.traceLinearMap (Fin r) ℂ ℂ).toContinuousLinearMap
  refine ⟨‖tr‖/(r : ℝ), div_nonneg (norm_nonneg _) (Nat.cast_nonneg _), ?_⟩
  intro X
  calc
    ‖normalizedMatrixAbsTrace X‖ = |(Matrix.trace (CFC.abs X)).re|/(r : ℝ) := by
      simp only [normalizedMatrixAbsTrace, norm_div, Real.norm_eq_abs, Nat.cast_nonneg,
        abs_of_nonneg, Fintype.card_fin]
    _ ≤ ‖Matrix.trace (CFC.abs X)‖/(r : ℝ) :=
      div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (Nat.cast_nonneg _)
    _ ≤ (‖tr‖*‖CFC.abs X‖)/(r : ℝ) :=
      div_le_div_of_nonneg_right (tr.le_opNorm _) (Nat.cast_nonneg _)
    _ = _ := by rw [CFC.norm_abs, Matrix.cstar_norm_def]; ring

end OperatorNorm

open scoped Matrix.Norms.Elementwise
local instance matrixAbsoluteIntegrabilityENormedAddMonoid {r : ℕ} :
    ENormedAddMonoid (Circulation.Mat r) :=
  inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))

theorem normalizedMatrixAbsTrace_memLp {r : ℕ} (F : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) :
    MemLp (fun t => normalizedMatrixAbsTrace (F t)) 2 circleMeasure := by
  let L : Circulation.Mat r →L[ℂ]
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.toContinuousLinearMap
  have hLF : MemLp (fun t => L (F t)) 2 circleMeasure := L.comp_memLp' hF
  have hL (X : Circulation.Mat r) : L X = Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) X := rfl
  obtain ⟨C,hC,hbound⟩ := normalizedMatrixAbsTrace_operator_bound (r := r)
  apply (hLF.norm.const_smul C).of_le
    (continuous_normalizedMatrixAbsTrace.comp_aestronglyMeasurable hF.aestronglyMeasurable)
  filter_upwards [] with t
  simpa only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hC, abs_of_nonneg (norm_nonneg _), hL] using hbound (F t)

theorem normalizedMatrixAbsTrace_integrable {r : ℕ} (F : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) :
    Integrable (fun t => normalizedMatrixAbsTrace (F t)) circleMeasure :=
  (normalizedMatrixAbsTrace_memLp F hF).integrable (by norm_num)

end
end CGLMPBounds.Hardy
