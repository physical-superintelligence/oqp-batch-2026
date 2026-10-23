module

public import CGLMPBounds.Hardy.HolomorphicPinchingRectangle

@[expose] public section


/-! The C.5 integrability obligation follows from the actual finite measure
and its compact support. Continuity is needed only on the support rectangle,
so the holomorphic function is never extended past its strip. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem positivePinching_continuousOn_rectangle_integrable
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {f : ℝ × ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1 ×ˢ
      Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y)))) :
    Integrable f (positivePinchingMeasure B Y) := by
  letI := positivePinching_measure_finite hB hB2 hY
  let K := Icc (-1 : ℝ) 1 ×ˢ Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y))
  have hin : IntegrableOn f K (positivePinchingMeasure B Y) :=
    hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hout : IntegrableOn f Kᶜ (positivePinchingMeasure B Y) := by
    have hz : (positivePinchingMeasure B Y).restrict Kᶜ = 0 :=
      Measure.restrict_eq_zero.mpr (positivePinching_measure_outside_rectangle hB hB2 hY)
    simp only [IntegrableOn, hz, integrable_zero_measure]
  simpa only [Set.union_compl_self, integrableOn_univ] using hin.union hout

theorem positivePinching_holomorphic_derivative_integrable
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f openVerticalUnitStrip)
    {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) (n : ℕ) :
    Integrable (fun p : ℝ × ℝ => iteratedDeriv n f (-(ρ : ℂ) * p.1 + Complex.I * p.2))
      (positivePinchingMeasure B Y) := by
  apply positivePinching_continuousOn_rectangle_integrable hB hB2 hY
  have hd : AnalyticOnNhd ℂ (iteratedDeriv n f) openVerticalUnitStrip := by
    simpa only [iteratedDeriv_eq_iterate] using hf.iterated_deriv n
  exact hd.continuousOn.comp (by fun_prop)
    (fun p hp => strip_argument_mem hρ hp.1)

end
end CGLMPBounds.Hardy
