module

public import CGLMPBounds.Hardy.HolomorphicPinchingParameter
public import CGLMPBounds.Hardy.CompactHolomorphicIntegral

@[expose] public section


/-! Holomorphy of the actual scalar integral in the C.5 parameter strip.
The finite positive measure is embedded in ℂ² only to apply joint analytic
calculus. Its exact pushforward is transported back. No measurability of f
outside its holomorphic strip is required or assumed. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem analyticOnNhd_positivePinching_parameter_integral
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {ρ : ℝ} (hρ : 0 ≤ ρ) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f openVerticalUnitStrip) (n : ℕ) :
    AnalyticOnNhd ℂ (fun t => ∫ p : ℝ × ℝ,
      iteratedDeriv n f (-(ρ : ℂ) * p.1 + t * p.2) ∂positivePinchingMeasure B Y)
      {t : ℂ | |t.re| < (1 - ρ) / (‖Y‖ + 1)} := by
  let ν := positivePinchingMeasure B Y
  letI : IsFiniteMeasure ν := positivePinching_measure_finite hB hB2 hY
  let K : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ
    Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y))
  let Ψ : ℝ × ℝ → ℂ × ℂ := fun p => ((p.1 : ℂ), (p.2 : ℂ))
  have hΨ : Continuous Ψ := by fun_prop
  let L : Set (ℂ × ℂ) := Ψ '' K
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hL : IsCompact L := hK.image hΨ
  let μ : Measure (ℂ × ℂ) := ν.map Ψ
  have hνK : ∀ᵐ p ∂ν, p ∈ K := by
    apply ae_iff.mpr
    exact positivePinching_measure_outside_rectangle hB hB2 hY
  have hμL : ∀ᵐ ζ ∂μ, ζ ∈ L := by
    apply (ae_map_iff hΨ.measurable.aemeasurable hL.measurableSet).mpr
    exact hνK.mono fun p hp => mem_image_of_mem Ψ hp
  have hrestrict : μ.restrict L = μ := Measure.restrict_eq_self_of_ae_mem hμL
  let S : Set ℂ := {t : ℂ | |t.re| < (1 - ρ) / (‖Y‖ + 1)}
  have hS : IsOpen S := isOpen_lt Complex.continuous_re.abs continuous_const
  let F : ℂ × (ℂ × ℂ) → ℂ := fun q =>
    iteratedDeriv n f (-(ρ : ℂ) * q.2.1 + q.1 * q.2.2)
  have hF : ∀ w ∈ S, ∀ ζ ∈ L, AnalyticAt ℂ F (w, ζ) := by
    intro w hw ζ hζ
    obtain ⟨p, hp, rfl⟩ := hζ
    have ha := positivePinching_parameter_scalar_mem_strip hY hρ hw hp
    have hx : AnalyticAt ℂ (fun q : ℂ × (ℂ × ℂ) => q.2.1) (w, Ψ p) := by
      simpa only [Function.comp_def] using
        (analyticAt_fst (𝕜 := ℂ) (p := Ψ p)).comp
          (f := fun q : ℂ × (ℂ × ℂ) => q.2) (x := (w, Ψ p))
          (analyticAt_snd (𝕜 := ℂ) (p := (w, Ψ p)))
    have hy : AnalyticAt ℂ (fun q : ℂ × (ℂ × ℂ) => q.2.2) (w, Ψ p) := by
      simpa only [Function.comp_def] using
        (analyticAt_snd (𝕜 := ℂ) (p := Ψ p)).comp
          (f := fun q : ℂ × (ℂ × ℂ) => q.2) (x := (w, Ψ p))
          (analyticAt_snd (𝕜 := ℂ) (p := (w, Ψ p)))
    have hw' : AnalyticAt ℂ (fun q : ℂ × (ℂ × ℂ) => q.1) (w, Ψ p) := analyticAt_fst
    have harg : AnalyticAt ℂ
        (fun q : ℂ × (ℂ × ℂ) => -(ρ : ℂ)*q.2.1+q.1*q.2.2) (w, Ψ p) :=
      (analyticAt_const.mul hx).add (hw'.mul hy)
    simpa only [F, Function.comp_def, iteratedDeriv_eq_iterate] using ((hf.iterated_deriv n) _ ha).comp (x := (w, Ψ p))
      (f := fun q : ℂ × (ℂ × ℂ) => -(ρ : ℂ) * q.2.1 + q.1 * q.2.2) harg
  have hmap (w : ℂ) (hw : w ∈ S) :
      (∫ ζ in L, F (w, ζ) ∂μ) =
        ∫ p : ℝ × ℝ, iteratedDeriv n f (-(ρ : ℂ) * p.1 + w * p.2) ∂ν := by
    have hc : ContinuousOn (fun ζ => F (w, ζ)) L := by
      intro ζ hζ
      exact ((hF w hw ζ hζ).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
    have hm : AEStronglyMeasurable (fun ζ => F (w, ζ)) μ := by
      simpa only [hrestrict] using hc.aestronglyMeasurable (μ := μ) hL.measurableSet
    rw [hrestrict]
    exact integral_map hΨ.measurable.aemeasurable hm
  intro t ht
  have hG := analyticAt_integral_compact_holomorphic hL μ (hF t ht)
  apply hG.congr
  filter_upwards [hS.mem_nhds ht] with w hw
  exact hmap w hw

end
end CGLMPBounds.Hardy
