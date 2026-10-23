module

public import Mathlib

@[expose] public section


/-! Holomorphic integration on compact subsets of an arbitrary complex
normed space. The second variable need not be one-dimensional, which lets
C.5 integrate over the genuine pair of real coordinates embedded in ℂ². -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def compactParameterDerivative (F : ℂ × E → ℂ) (w : ℂ) (ζ : E) : ℂ :=
  fderiv ℂ F (w, ζ) (1, 0)

lemma hasDerivAt_compactSlice {F : ℂ × E → ℂ} {w : ℂ} {ζ : E}
    (hF : AnalyticAt ℂ F (w, ζ)) :
    HasDerivAt (fun v => F (v, ζ)) (compactParameterDerivative F w ζ) w := by
  have hd := hF.differentiableAt.hasFDerivAt.comp w
    (hasFDerivAt_prodMk_left (𝕜 := ℂ) w ζ)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, compactParameterDerivative] using hd.hasDerivAt

lemma continuousAt_compactParameterDerivative {F : ℂ × E → ℂ} {p : ℂ × E}
    (hF : AnalyticAt ℂ F p) :
    ContinuousAt (fun q : ℂ × E => compactParameterDerivative F q.1 q.2) p := by
  let ev : ((ℂ × E) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1, 0)
  exact ev.continuous.continuousAt.comp hF.fderiv.continuousAt

theorem hasDerivAt_integral_compact_holomorphic
    {F : ℂ × E → ℂ} {z : ℂ} {K : Set E} (hK : IsCompact K)
    (μ : Measure E) [IsFiniteMeasure μ]
    (hF : ∀ᶠ w in 𝓝 z, ∀ ζ ∈ K, AnalyticAt ℂ F (w, ζ)) :
    HasDerivAt (fun w => ∫ ζ in K, F (w, ζ) ∂μ)
      (∫ ζ in K, compactParameterDerivative F z ζ ∂μ) z := by
  have hF0 : ∀ ζ ∈ K, AnalyticAt ℂ F (z, ζ) := hF.self_of_nhds
  have hcont (w : ℂ) (hw : ∀ ζ ∈ K, AnalyticAt ℂ F (w, ζ)) :
      ContinuousOn (fun ζ => F (w, ζ)) K := by
    intro ζ hζ
    exact ((hw ζ hζ).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hD0 : ContinuousOn (compactParameterDerivative F z) K := by
    intro ζ hζ
    exact ((continuousAt_compactParameterDerivative (hF0 ζ hζ)).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hD0
  have hbound : ∀ᶠ w in 𝓝 z, ∀ ζ ∈ K,
      ‖compactParameterDerivative F w ζ‖ ≤ M + 1 := by
    apply hK.eventually_forall_of_forall_eventually
    intro ζ hζ
    have hc := (continuousAt_compactParameterDerivative (hF0 ζ hζ)).norm
    exact (hc.eventually_lt continuousAt_const
      ((hM ζ hζ).trans_lt (lt_add_one M))).mono fun _ h => h.le
  let S : Set ℂ := {w | (∀ ζ ∈ K, AnalyticAt ℂ F (w, ζ)) ∧
    ∀ ζ ∈ K, ‖compactParameterDerivative F w ζ‖ ≤ M + 1}
  have hmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (fun ζ => F (w, ζ)) (μ.restrict K) := by
    filter_upwards [hF] with w hw
    exact (hcont w hw).aestronglyMeasurable hK.measurableSet
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.restrict K) (F := fun w ζ => F (w, ζ))
    (F' := compactParameterDerivative F) (bound := fun _ => M + 1)
    (show S ∈ 𝓝 z from hF.and hbound) hmeas
    ((hcont z hF0).integrableOn_compact hK)
    (hD0.aestronglyMeasurable hK.measurableSet)
    ((ae_restrict_mem hK.measurableSet).mono fun ζ hζ w hw => hw.2 ζ hζ)
    (integrable_const (M + 1))
    ((ae_restrict_mem hK.measurableSet).mono fun ζ hζ w hw =>
      hasDerivAt_compactSlice (hw.1 ζ hζ))).2

theorem analyticAt_integral_compact_holomorphic
    {F : ℂ × E → ℂ} {z : ℂ} {K : Set E} (hK : IsCompact K)
    (μ : Measure E) [IsFiniteMeasure μ]
    (hF : ∀ ζ ∈ K, AnalyticAt ℂ F (z, ζ)) :
    AnalyticAt ℂ (fun w => ∫ ζ in K, F (w, ζ) ∂μ) z := by
  have he : ∀ᶠ w in 𝓝 z, ∀ ζ ∈ K, AnalyticAt ℂ F (w, ζ) :=
    hK.eventually_forall_of_forall_eventually (fun ζ hζ => (hF ζ hζ).eventually_analyticAt)
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [he.eventually_nhds] with w hw
  exact (hasDerivAt_integral_compact_holomorphic hK μ hw).differentiableAt

end
end CGLMPBounds.Hardy
