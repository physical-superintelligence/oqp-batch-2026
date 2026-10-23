module

public import CGLMPBounds.Hardy.CirclePoissonKernel
public import CGLMPBounds.Hardy.MatrixEntryIntegration
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section


/-! Genuine analyticity of the explicit Poisson/Herglotz matrix extension.
A positive distance to the unit circle supplies an integrable derivative
majorant. Scalar coordinate integrals are assembled in the finite matrix
basis, without changing the matrix norm instance. -/
namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter MeasureTheory Complex Metric
open scoped Topology Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

lemma circleHerglotzKernel_norm_le {z : ℂ} (hz : ‖z‖ < 1) (t : UnitCircle) :
    ‖circleHerglotzKernel z t‖ ≤ (1+‖z‖)/(1-‖z‖) := by
  have hl : 1-‖z‖ ≤ ‖fourier 1 t-z‖ := by
    simpa only [circle_fourier_norm] using norm_sub_norm_le (fourier 1 t) z
  have hu : ‖fourier 1 t+z‖ ≤ 1+‖z‖ := by simpa only [circle_fourier_norm] using norm_add_le (fourier 1 t) z
  rw [circleHerglotzKernel,norm_div]
  exact div_le_div₀ (by positivity) hu (by linarith) hl

lemma circleHerglotz_mul_integrable {z : ℂ} (hz : ‖z‖ < 1)
    {f : UnitCircle → ℂ} (hf : Integrable f circleMeasure) :
    Integrable (fun t => circleHerglotzKernel z t * f t) circleMeasure := by
  apply (hf.norm.const_mul ((1+‖z‖)/(1-‖z‖))).mono'
    ((continuous_circleHerglotzKernel hz).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (circleHerglotzKernel_norm_le hz t) (norm_nonneg _)

lemma hasDerivAt_circleHerglotzKernel {z : ℂ} (hz : ‖z‖ < 1) (t : UnitCircle) :
    HasDerivAt (fun w => circleHerglotzKernel w t) (2*fourier 1 t/(fourier 1 t-z)^2) z := by
  have h := ((hasDerivAt_const z (fourier 1 t)).fun_add (hasDerivAt_id z)).div
    ((hasDerivAt_const z (fourier 1 t)).fun_sub (hasDerivAt_id z))
    (circleHerglotz_denominator_ne hz t)
  change HasDerivAt (fun w => (fourier 1 t + w) / (fourier 1 t - w)) _ z at h
  change HasDerivAt (fun w => (fourier 1 t + w) / (fourier 1 t - w))
    (2*fourier 1 t/(fourier 1 t-z)^2) z
  apply h.congr_deriv
  simp only [id_eq]
  ring

lemma hasDerivAt_circleHerglotz_integral {z : ℂ} (hz : ‖z‖ < 1)
    {f : UnitCircle → ℂ} (hf : Integrable f circleMeasure) :
    HasDerivAt (fun w => ∫ t, circleHerglotzKernel w t*f t ∂circleMeasure)
      (∫ t, (2*fourier 1 t/(fourier 1 t-z)^2)*f t ∂circleMeasure) z := by
  let δ : ℝ := (1-‖z‖)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hnear {w : ℂ} (hw : w ∈ ball z δ) : ‖w‖ < 1-δ := by
    have hn := norm_sub_norm_le w z
    rw [mem_ball,dist_eq_norm] at hw
    dsimp [δ] at *
    linarith
  have hnorm {w : ℂ} (hw : w ∈ ball z δ) (t : UnitCircle) :
      ‖(2*fourier 1 t/(fourier 1 t-w)^2)*f t‖ ≤ (2/δ^2)*‖f t‖ := by
    have hd : δ ≤ ‖fourier 1 t-w‖ := by
      have hl := norm_sub_norm_le (fourier 1 t) w
      rw [circle_fourier_norm] at hl
      linarith [hnear hw]
    rw [norm_mul,norm_div,norm_mul,norm_pow,circle_fourier_norm]
    norm_num only [norm_ofNat,mul_one]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
      (by nlinarith [norm_nonneg (fourier 1 t-w)])
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := circleMeasure) (F := fun w t => circleHerglotzKernel w t*f t)
    (F' := fun w t => (2*fourier 1 t/(fourier 1 t-w)^2)*f t)
    (bound := fun t => (2/δ^2)*‖f t‖) (s := ball z δ)
    (Metric.ball_mem_nhds z hδ) _ (circleHerglotz_mul_integrable hz hf) _ _
    (hf.norm.const_mul _) _).2
  · filter_upwards [Metric.ball_mem_nhds z hδ] with w hw
    exact (circleHerglotz_mul_integrable (by linarith [hnear hw]) hf).aestronglyMeasurable
  · apply AEStronglyMeasurable.mul _ hf.aestronglyMeasurable
    apply Continuous.aestronglyMeasurable
    exact (continuous_const.mul (fourier 1).continuous).div
      (((fourier 1).continuous.sub continuous_const).pow 2)
      (fun t => pow_ne_zero _ (circleHerglotz_denominator_ne hz t))
  · exact Eventually.of_forall fun t w hw => hnorm hw t
  · exact Eventually.of_forall fun t w hw =>
      (hasDerivAt_circleHerglotzKernel (by linarith [hnear hw]) t).mul_const (f t)

lemma analyticAt_circleHerglotz_integral {z : ℂ} (hz : ‖z‖ < 1)
    {f : UnitCircle → ℂ} (hf : Integrable f circleMeasure) :
    AnalyticAt ℂ (fun w => ∫ t, circleHerglotzKernel w t*f t ∂circleMeasure) z := by
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
  exact (hasDerivAt_circleHerglotz_integral hw hf).differentiableAt

lemma matrixPoissonAnalytic_integral {r : ℕ} (B : UnitCircle → Circulation.Mat r)
    (hB : Integrable B circleMeasure) {z : ℂ} (hz : ‖z‖ < 1) :
    matrixPoissonAnalytic B z = ∫ t, circleHerglotzKernel z t • B t ∂circleMeasure := by
  have hi : Integrable (fun t => circleHerglotzKernel z t • B t) circleMeasure := by
    apply (hB.norm.const_mul ((1+‖z‖)/(1-‖z‖))).mono'
      ((continuous_circleHerglotzKernel hz).aestronglyMeasurable.smul hB.aestronglyMeasurable)
    exact Eventually.of_forall fun t => by
      rw [Pi.smul_apply', norm_smul]
      exact mul_le_mul_of_nonneg_right (circleHerglotzKernel_norm_le hz t) (norm_nonneg _)
  ext i j
  rw [matrix_integral_entry hi]
  rfl

theorem matrixPoissonAnalytic_analytic {r : ℕ} (B : UnitCircle → Circulation.Mat r)
    (hB : Integrable B circleMeasure) :
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
  apply analyticAt_circleHerglotz_integral (by simpa [mem_ball,dist_zero_right] using hz)
  exact (matrixEntryCLM i j).integrable_comp hB

theorem matrixPoissonAnalytic_zero {r : ℕ} (B : UnitCircle → Circulation.Mat r)
    (hB : Integrable B circleMeasure) :
    matrixPoissonAnalytic B 0 = ∫ t, B t ∂circleMeasure := by
  rw [matrixPoissonAnalytic_integral B hB (by norm_num)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    simp [circleHerglotzKernel,circle_fourier_ne_zero]

end
end CGLMPBounds.Hardy
