module

public import CGLMPBounds.Hardy.SchwarzContourCoefficients
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section


/-! Holomorphic parameter integration against an actual finite measure on a
compact set, for C.5. Compactness supplies the uniform derivative bound;
analyticity, derivative interchange and integrability are conclusions. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

lemma continuousOn_compact_analytic_slice {F : ℂ × ℂ → ℂ} {z : ℂ} {K : Set ℂ}
    (hF : ∀ ζ ∈ K, AnalyticAt ℂ F (z, ζ)) :
    ContinuousOn (fun ζ => F (z, ζ)) K := by
  intro ζ hζ
  exact ((hF ζ hζ).continuousAt.comp
    (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt

theorem hasDerivAt_integral_compact_joint_analytic
    {F : ℂ × ℂ → ℂ} {z : ℂ} {K : Set ℂ} (hK : IsCompact K)
    (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hF : ∀ᶠ w in 𝓝 z, ∀ ζ ∈ K, AnalyticAt ℂ F (w, ζ)) :
    HasDerivAt (fun w => ∫ ζ in K, F (w, ζ) ∂μ)
      (∫ ζ in K, circleParameterDerivative F z ζ ∂μ) z := by
  have hF0 : ∀ ζ ∈ K, AnalyticAt ℂ F (z, ζ) := hF.self_of_nhds
  have hD0 : ContinuousOn (circleParameterDerivative F z) K := by
    intro ζ hζ
    exact ((continuousAt_circleParameterDerivative (hF0 ζ hζ)).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hD0
  have hbound : ∀ᶠ w in 𝓝 z, ∀ ζ ∈ K,
      ‖circleParameterDerivative F w ζ‖ ≤ M + 1 := by
    apply hK.eventually_forall_of_forall_eventually
    intro ζ hζ
    have hc := (continuousAt_circleParameterDerivative (hF0 ζ hζ)).norm
    have hlt : ‖circleParameterDerivative F z ζ‖ < M + 1 :=
      (hM ζ hζ).trans_lt (lt_add_one M)
    exact (hc.eventually_lt continuousAt_const hlt).mono fun _ h => h.le
  let S : Set ℂ := {w | (∀ ζ ∈ K, AnalyticAt ℂ F (w, ζ)) ∧
    ∀ ζ ∈ K, ‖circleParameterDerivative F w ζ‖ ≤ M + 1}
  have hS : S ∈ 𝓝 z := hF.and hbound
  have hmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (fun ζ => F (w, ζ)) (μ.restrict K) := by
    filter_upwards [hF] with w hw
    exact (continuousOn_compact_analytic_slice hw).aestronglyMeasurable hK.measurableSet
  have hint : Integrable (fun ζ => F (z, ζ)) (μ.restrict K) :=
    (continuousOn_compact_analytic_slice hF0).integrableOn_compact hK
  have hdmeas : AEStronglyMeasurable (circleParameterDerivative F z) (μ.restrict K) :=
    hD0.aestronglyMeasurable hK.measurableSet
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.restrict K) (F := fun w ζ => F (w, ζ))
    (F' := circleParameterDerivative F) (bound := fun _ => M + 1)
    hS hmeas hint hdmeas
    ((ae_restrict_mem hK.measurableSet).mono fun ζ hζ w hw => hw.2 ζ hζ)
    (integrable_const (M + 1))
    ((ae_restrict_mem hK.measurableSet).mono fun ζ hζ w hw =>
      hasDerivAt_circleSlice (hw.1 ζ hζ))).2

theorem analyticAt_integral_compact_joint
    {F : ℂ × ℂ → ℂ} {z : ℂ} {K : Set ℂ} (hK : IsCompact K)
    (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hF : ∀ ζ ∈ K, AnalyticAt ℂ F (z, ζ)) :
    AnalyticAt ℂ (fun w => ∫ ζ in K, F (w, ζ) ∂μ) z := by
  have he : ∀ᶠ w in 𝓝 z, ∀ ζ ∈ K, AnalyticAt ℂ F (w, ζ) :=
    hK.eventually_forall_of_forall_eventually (fun ζ hζ => (hF ζ hζ).eventually_analyticAt)
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [he.eventually_nhds] with w hw
  exact (hasDerivAt_integral_compact_joint_analytic hK μ hw).differentiableAt

lemma iteratedDeriv_integral_compact_joint_aux (n : ℕ)
    {F : ℂ × ℂ → ℂ} {z : ℂ} {K : Set ℂ} (hK : IsCompact K)
    (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hF : ∀ᶠ w in 𝓝 z, ∀ ζ ∈ K, AnalyticAt ℂ F (w, ζ)) :
    iteratedDeriv n (fun w => ∫ ζ in K, F (w, ζ) ∂μ) z =
      ∫ ζ in K, jointCircleIteratedDerivative n F (z, ζ) ∂μ := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have he : deriv (fun w => ∫ ζ in K, F (w, ζ) ∂μ) =ᶠ[𝓝 z]
        (fun w => ∫ ζ in K, jointCircleDerivative F (w, ζ) ∂μ) := by
      filter_upwards [hF.eventually_nhds] with w hw
      exact (hasDerivAt_integral_compact_joint_analytic hK μ hw).deriv
    rw [he.iteratedDeriv_eq n]
    exact ih (hF.mono fun w hw ζ hζ => analyticAt_jointCircleDerivative (hw ζ hζ))

theorem iteratedDeriv_integral_compact_joint (n : ℕ)
    {F : ℂ × ℂ → ℂ} {z : ℂ} {K : Set ℂ} (hK : IsCompact K)
    (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hF : ∀ ζ ∈ K, AnalyticAt ℂ F (z, ζ)) :
    iteratedDeriv n (fun w => ∫ ζ in K, F (w, ζ) ∂μ) z =
      ∫ ζ in K, iteratedDeriv n (fun w => F (w, ζ)) z ∂μ := by
  have he : ∀ᶠ w in 𝓝 z, ∀ ζ ∈ K, AnalyticAt ℂ F (w, ζ) :=
    hK.eventually_forall_of_forall_eventually (fun ζ hζ => (hF ζ hζ).eventually_analyticAt)
  rw [iteratedDeriv_integral_compact_joint_aux n hK μ he]
  apply setIntegral_congr_fun hK.measurableSet
  intro ζ hζ
  exact (iteratedDeriv_circleSlice_eq n (hF ζ hζ)).symm

end
end CGLMPBounds.Hardy
