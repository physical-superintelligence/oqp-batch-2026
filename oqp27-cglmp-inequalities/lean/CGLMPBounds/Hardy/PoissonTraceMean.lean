module

public import CGLMPBounds.Hardy.PoissonStrictStrip
public import CGLMPBounds.Hardy.HolomorphicTraceAnalytic
public import CGLMPBounds.Hardy.HardyPotentialAnalytic
public import Mathlib.Analysis.Complex.MeanValue

@[expose] public section


/-! Actual holomorphic root trace and its normalized circle mean for the
explicit Poisson extension. Entrywise analyticity bridges the equivalent
matrix norm instances explicitly. Algebraic multiplicities are retained. -/
namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter MeasureTheory Complex Metric
open scoped Topology
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

lemma circle_haar_integral_eq_circleAverage (f : ℂ → ℂ) (ρ : ℝ) :
    (∫ t : UnitCircle, f ((ρ : ℂ)*fourier 1 t) ∂circleMeasure) =
      Real.circleAverage f 0 ρ := by
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0]
  simp only [inv_one,one_smul,zero_add]
  have hchange := intervalIntegral.smul_integral_comp_mul_right
    (fun θ : ℝ => f (circleMap 0 ρ θ)) (2*Real.pi) (a := 0) (b := 1)
  simp only [zero_mul,one_mul] at hchange
  have he : (fun t : ℝ => f ((ρ : ℂ)*fourier 1 (t : UnitCircle))) =
      (fun t : ℝ => f (circleMap 0 ρ (t*(2*Real.pi)))) := by
    funext t
    congr 1
    rw [fourier_coe_apply]
    simp only [circleMap,zero_add,Int.cast_one,mul_one,div_one,Complex.ofReal_mul]
    push_cast
    congr 2
    ring
  rw [he,Real.circleAverage]
  rw [← hchange,smul_smul]
  rw [inv_mul_cancel₀ (show (2*Real.pi : ℝ) ≠ 0 by positivity), one_smul]

section RowOperatorBridge
open scoped Matrix.Norms.Operator

lemma matrixPoissonAnalytic_analytic_row_of_entries {r : ℕ}
    (B : UnitCircle → Circulation.Mat r)
    (hB : ∀ i j, Integrable (fun t => B t i j) circleMeasure) :
    AnalyticOnNhd ℂ (matrixPoissonAnalytic B) (ball 0 1) := by
  intro z hz
  have he : matrixPoissonAnalytic B = fun w => ∑ i : Fin r, ∑ j : Fin r,
      (∫ t, circleHerglotzKernel w t * B t i j ∂circleMeasure) • Matrix.single i j 1 := by
    funext w
    ext i j
    simp [matrixPoissonAnalytic,Matrix.sum_apply,Matrix.single_apply,ite_and]
  rw [he]
  apply Finset.analyticAt_fun_sum
  intro i _
  apply Finset.analyticAt_fun_sum
  intro j _
  apply AnalyticAt.fun_smul (g := fun _ => Matrix.single i j (1 : ℂ)) _ analyticAt_const
  exact analyticAt_circleHerglotz_integral (by simpa [mem_ball,dist_zero_right] using hz) (hB i j)

end RowOperatorBridge

section L2Operator
open scoped Matrix.Norms.L2Operator

lemma poisson_normalized_root_trace_analytic {r : ℕ}
    (B : UnitCircle → Circulation.Mat r) (hB : AEStronglyMeasurable B circleMeasure)
    (hherm : ∀ᵐ t ∂circleMeasure, (B t).IsHermitian)
    (hbound : ∀ᵐ t ∂circleMeasure, ‖B t‖ ≤ 1)
    (hmean : (∫ t, B t ∂circleMeasure)=0) :
    AnalyticOnNhd ℂ (fun z => normalizedSpectralTrace hardyStripPotential
      (matrixPoissonAnalytic B z)) (ball 0 1) := by
  intro z hz
  apply analyticAt_normalizedSpectralTrace
    (isOpen_lt Complex.continuous_re.abs continuous_const)
    (matrixPoissonAnalytic_analytic_row_of_entries B
      (fun i j => (matrixEntryCLM i j).integrable_comp
        (circle_bounded_matrix_integrable hB hbound)) z hz)
    analyticOnNhd_hardyStripPotential
  intro w hw
  exact matrixPoissonAnalytic_spectrum_strict_strip B hB hherm hbound hmean
    (by simpa [mem_ball,dist_zero_right] using hz) w hw

lemma normalizedSpectralTrace_zero {r : ℕ} (hr : 0 < r) (f : ℂ → ℂ) :
    normalizedSpectralTrace f (0 : Circulation.Mat r) = f 0 := by
  rw [normalizedSpectralTrace,Matrix.charpoly_zero,Polynomial.roots_X_pow]
  simp only [Fintype.card_fin,Multiset.nsmul_singleton,Multiset.map_replicate,Multiset.sum_replicate,nsmul_eq_mul]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  field_simp

theorem matrixPoissonRadial_potential_mean {r : ℕ} (hr : 0 < r)
    (B : UnitCircle → Circulation.Mat r) (hB : AEStronglyMeasurable B circleMeasure)
    (hherm : ∀ᵐ t ∂circleMeasure, (B t).IsHermitian)
    (hbound : ∀ᵐ t ∂circleMeasure, ‖B t‖ ≤ 1)
    (hmean : (∫ t, B t ∂circleMeasure)=0)
    {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    Integrable (fun t => matrixHardyPotential (matrixPoissonRadial B ρ t)) circleMeasure ∧
    (∫ t, matrixHardyPotential (matrixPoissonRadial B ρ t) ∂circleMeasure) =
      hardyStripCenterConstant := by
  let f : ℂ → ℂ := fun z => normalizedSpectralTrace hardyStripPotential (matrixPoissonAnalytic B z)
  have ha : AnalyticOnNhd ℂ f (ball 0 1) :=
    poisson_normalized_root_trace_analytic B hB hherm hbound hmean
  have hsmall : closedBall (0 : ℂ) |ρ| ⊆ ball 0 1 := by
    rw [abs_of_nonneg hρ.1]
    exact closedBall_subset_ball hρ.2
  have hc : Continuous (fun t : UnitCircle => f ((ρ : ℂ)*fourier 1 t)) := by
    apply ha.continuousOn.comp_continuous
      (continuous_const.mul (fourier 1).continuous)
    intro t
    simpa only [Pi.mul_apply,mem_ball,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hρ.1,circle_fourier_norm,mul_one] using hρ.2
  have hi : Integrable (fun t : UnitCircle => f ((ρ : ℂ)*fourier 1 t)) circleMeasure :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hi.re, ?_⟩
  change (∫ t : UnitCircle, (f ((ρ : ℂ)*fourier 1 t)).re ∂circleMeasure)=_
  have hre : (∫ t : UnitCircle, (f ((ρ : ℂ)*fourier 1 t)).re ∂circleMeasure) =
      (∫ t : UnitCircle, f ((ρ : ℂ)*fourier 1 t) ∂circleMeasure).re := by
    simpa only [RCLike.re_to_complex] using integral_re hi
  rw [hre,circle_haar_integral_eq_circleAverage]
  have hmv : Real.circleAverage f 0 ρ=f 0 := by
    apply circleAverage_of_differentiable_on_off_countable (s := ∅) Set.countable_empty
      (ha.continuousOn.mono hsmall)
    intro z hz
    exact (ha z (hsmall (ball_subset_closedBall hz.1))).differentiableAt
  rw [hmv]
  dsimp [f]
  rw [matrixPoissonAnalytic_zero B (circle_bounded_matrix_integrable hB hbound),hmean,
    normalizedSpectralTrace_zero hr]
  simp [hardyStripPotential,segmentPrimitive]

end L2Operator
end
end CGLMPBounds.Hardy
