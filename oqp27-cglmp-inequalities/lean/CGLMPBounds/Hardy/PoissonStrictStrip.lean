module

public import CGLMPBounds.Hardy.PoissonAnalytic

@[expose] public section


/-! The real part of the actual extension is the actual Poisson average.
Subtracting the positive constant lower bound from the kernel uses the
zero mean and yields a uniform strict numerical-range bound in the disk. -/
namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter MeasureTheory Complex Metric
open scoped Topology Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

lemma circle_bounded_matrix_integrable {r : ℕ} {B : UnitCircle → Circulation.Mat r}
    (hB : AEStronglyMeasurable B circleMeasure)
    (hbound : ∀ᵐ t ∂circleMeasure, ‖B t‖ ≤ 1) : Integrable B circleMeasure :=
  (integrable_const (1 : ℝ)).mono' hB hbound

lemma circle_continuous_smul_bounded_integrable {r : ℕ}
    {B : UnitCircle → Circulation.Mat r} (hB : AEStronglyMeasurable B circleMeasure)
    (hbound : ∀ᵐ t ∂circleMeasure, ‖B t‖ ≤ 1) {g : UnitCircle → ℂ} (hg : Continuous g) :
    Integrable (fun t => g t • B t) circleMeasure := by
  apply (hg.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mono'
    (hg.aestronglyMeasurable.smul hB)
  filter_upwards [hbound] with t ht
  change ‖g t • B t‖ ≤ ‖g t‖
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) ht

theorem matrixPoissonAnalytic_realPart {r : ℕ} (B : UnitCircle → Circulation.Mat r)
    (hB : AEStronglyMeasurable B circleMeasure)
    (hherm : ∀ᵐ t ∂circleMeasure, (B t).IsHermitian)
    (hbound : ∀ᵐ t ∂circleMeasure, ‖B t‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    hermitianRealPart (matrixPoissonAnalytic B z) =
      ∫ t, (circlePoissonKernel z t : ℂ) • B t ∂circleMeasure := by
  rw [matrixPoissonAnalytic_integral B (circle_bounded_matrix_integrable hB hbound) hz,
    hermitianRealPart_integral
      (circle_continuous_smul_bounded_integrable hB hbound (continuous_circleHerglotzKernel hz))]
  apply integral_congr_ae
  exact hherm.mono fun t ht => hermitianRealPart_smul_of_hermitian ht _

theorem matrixPoissonAnalytic_realPart_norm {r : ℕ}
    (B : UnitCircle → Circulation.Mat r) (hB : AEStronglyMeasurable B circleMeasure)
    (hherm : ∀ᵐ t ∂circleMeasure, (B t).IsHermitian)
    (hbound : ∀ᵐ t ∂circleMeasure, ‖B t‖ ≤ 1)
    (hmean : (∫ t, B t ∂circleMeasure)=0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖hermitianRealPart (matrixPoissonAnalytic B z)‖ ≤ 2*‖z‖/(1+‖z‖) := by
  let c : ℝ := (1-‖z‖)/(1+‖z‖)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hp : ∀ t, 0 ≤ circlePoissonKernel z t-c := fun t =>
    sub_nonneg.mpr (circlePoissonKernel_lower hz t)
  have hg : Continuous (fun t => ((circlePoissonKernel z t-c : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((circlePoissonKernel_continuous hz).sub continuous_const)
  have hgi := circle_continuous_smul_bounded_integrable hB hbound hg
  have hPi := circle_continuous_smul_bounded_integrable hB hbound
    (Complex.continuous_ofReal.comp (circlePoissonKernel_continuous hz))
  have hBi := circle_bounded_matrix_integrable hB hbound
  have he : hermitianRealPart (matrixPoissonAnalytic B z) =
      ∫ t, ((circlePoissonKernel z t-c : ℝ) : ℂ) • B t ∂circleMeasure := by
    rw [matrixPoissonAnalytic_realPart B hB hherm hbound hz]
    simp_rw [Complex.ofReal_sub,sub_smul]
    have hsub := integral_sub hPi (hBi.smul (c : ℂ))
    simp only [Function.comp_apply, Pi.smul_apply] at hsub
    rw [hsub,integral_smul,hmean,smul_zero,sub_zero]
  have hscalar : Integrable (fun t => circlePoissonKernel z t-c) circleMeasure :=
    ((circlePoissonKernel_continuous hz).sub continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [he]
  calc
    _ ≤ ∫ t, ‖((circlePoissonKernel z t-c : ℝ) : ℂ) • B t‖ ∂circleMeasure :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, circlePoissonKernel z t-c ∂circleMeasure := by
      apply integral_mono_ae hgi.norm hscalar
      filter_upwards [hbound] with t ht
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp t)]
      exact mul_le_of_le_one_right (hp t) ht
    _ = 2*‖z‖/(1+‖z‖) := by
      rw [integral_sub
        ((circlePoissonKernel_continuous hz).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) (integrable_const _),
        circlePoissonKernel_integral hz,integral_const]
      simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul,smul_eq_mul,one_mul,c]
      field_simp [show (1+‖z‖) ≠ 0 by positivity]
      ring

theorem matrixPoissonAnalytic_spectrum_strict_strip {r : ℕ}
    (B : UnitCircle → Circulation.Mat r) (hB : AEStronglyMeasurable B circleMeasure)
    (hherm : ∀ᵐ t ∂circleMeasure, (B t).IsHermitian)
    (hbound : ∀ᵐ t ∂circleMeasure, ‖B t‖ ≤ 1)
    (hmean : (∫ t, B t ∂circleMeasure)=0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ∀ w ∈ spectrum ℂ (matrixPoissonAnalytic B z), |w.re| < 1 := by
  intro w hw
  have h := (matrix_spectrum_parts_rectangle (matrixPoissonAnalytic B z) hw).1.trans
    (matrixPoissonAnalytic_realPart_norm B hB hherm hbound hmean hz)
  apply h.trans_lt
  apply (div_lt_iff₀ (show 0 < 1+‖z‖ by positivity)).mpr
  linarith

end
end CGLMPBounds.Hardy
