module

public import CGLMPBounds.Hardy.HolomorphicPinchingLocal
public import CGLMPBounds.Hardy.HolomorphicPinchingIntegrability

@[expose] public section


/-! Literal C.5. The local holomorphic moment identity is continued in
the actual complex matrix parameter through a connected vertical strip
containing 0 and i. Both the full algebraic-multiplicity spectral trace
and the actual positive-measure integral are analytic on that strip.
The final minus sign is exactly i². -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem positivePinching_holomorphic_parameter
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f openVerticalUnitStrip)
    {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) {t : ℂ}
    (ht : |t.re| < (1 - ρ) / (‖Y‖ + 1)) :
    normalizedSpectralTrace f ((ρ : ℂ) • B + t • Y) -
      normalizedSpectralTrace f ((ρ : ℂ) • B + t • positivePinchingPart B Y) =
      t ^ 2 * ∫ p : ℝ × ℝ, iteratedDeriv 2 f (-(ρ : ℂ) * p.1 + t * p.2)
        ∂positivePinchingMeasure B Y := by
  let δ : ℝ := (1 - ρ) / (‖Y‖ + 1)
  let S : Set ℂ := {t : ℂ | |t.re| < δ}
  have hδ : 0 < δ := div_pos (sub_pos.mpr hρ.2) (by positivity)
  have hS : Convex ℝ S := by
    have hs : S = {z : ℂ | -δ < z.re} ∩ {z : ℂ | z.re < δ} := by
      ext z
      change |z.re| < δ ↔ -δ < z.re ∧ z.re < δ
      exact abs_lt
    rw [hs]
    exact (convex_halfSpace_re_gt (-δ)).inter (convex_halfSpace_re_lt δ)
  have hG := analyticOnNhd_positivePinching_parameter_trace hB hB2 hY hρ.1 hf
  have hH : AnalyticOnNhd ℂ (fun t => t ^ 2 * ∫ p : ℝ × ℝ,
      iteratedDeriv 2 f (-(ρ : ℂ) * p.1 + t * p.2) ∂positivePinchingMeasure B Y) S :=
    (analyticOnNhd_id.pow 2).mul
      (analyticOnNhd_positivePinching_parameter_integral hB hB2 hY hρ.1 hf 2)
  exact hG.eqOn_of_preconnected_of_eventuallyEq hH hS.isPreconnected
    (by simpa only [S, mem_setOf_eq, Complex.zero_re, abs_zero] using hδ)
    (positivePinching_holomorphic_local hB hB2 hY hρ hf) ht

theorem positivePinching_holomorphic_strip
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f openVerticalUnitStrip)
    {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    Integrable (fun p : ℝ × ℝ => iteratedDeriv 2 f (-(ρ : ℂ) * p.1 + Complex.I * p.2))
      (positivePinchingMeasure B Y) ∧
    normalizedSpectralTrace f ((ρ : ℂ) • B + Complex.I • Y) -
      normalizedSpectralTrace f ((ρ : ℂ) • B + Complex.I • positivePinchingPart B Y) =
        -(∫ p : ℝ × ℝ, iteratedDeriv 2 f (-(ρ : ℂ) * p.1 + Complex.I * p.2)
          ∂positivePinchingMeasure B Y) := by
  constructor
  · exact positivePinching_holomorphic_derivative_integrable hB hB2 hY hf hρ 2
  · have ht : |Complex.I.re| < (1 - ρ) / (‖Y‖ + 1) := by
      simp only [Complex.I_re, abs_zero]
      exact div_pos (sub_pos.mpr hρ.2) (by positivity)
    simpa only [Complex.I_sq, neg_one_mul] using
      positivePinching_holomorphic_parameter hB hB2 hY hf hρ ht

end
end CGLMPBounds.Hardy
