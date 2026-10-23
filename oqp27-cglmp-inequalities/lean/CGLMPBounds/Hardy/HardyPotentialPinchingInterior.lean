module

public import CGLMPBounds.Hardy.HardyPotentialAnalytic
public import CGLMPBounds.Hardy.HolomorphicPinching

@[expose] public section


/-! The genuine interior pinching identity and inequality for the C.14
potential. This is the pre-limit form of C.15. No boundary-limit or trace
absolute-value identification is asserted by these interior statements. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem hardyPotential_interior_pinching
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    Integrable (fun p : ℝ × ℝ => hardyStripSecant (-(ρ : ℂ) * p.1 + Complex.I * p.2))
      (positivePinchingMeasure B Y) ∧
    (normalizedSpectralTrace hardyStripPotential ((ρ : ℂ) • B + Complex.I • Y)).re -
      (normalizedSpectralTrace hardyStripPotential
        ((ρ : ℂ) • B + Complex.I • positivePinchingPart B Y)).re =
      ∫ p : ℝ × ℝ, (hardyStripSecant (-(ρ : ℂ) * p.1 + Complex.I * p.2)).re
        ∂positivePinchingMeasure B Y := by
  have hbase := positivePinching_holomorphic_strip hB hB2 hY hardyStripPotential
    analyticOnNhd_hardyStripPotential hρ
  have hν : ∀ᵐ p ∂positivePinchingMeasure B Y,
      p ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y)) := by
    apply ae_iff.mpr
    exact positivePinching_measure_outside_rectangle hB hB2 hY
  have he : (fun p : ℝ × ℝ => iteratedDeriv 2 hardyStripPotential
      (-(ρ : ℂ) * p.1 + Complex.I * p.2)) =ᵐ[positivePinchingMeasure B Y]
      (fun p => -hardyStripSecant (-(ρ : ℂ) * p.1 + Complex.I * p.2)) :=
    hν.mono fun p hp => hardyStripPotential_second_derivative (strip_argument_mem hρ hp.1)
  have hint : Integrable (fun p : ℝ × ℝ =>
      hardyStripSecant (-(ρ : ℂ) * p.1 + Complex.I * p.2)) (positivePinchingMeasure B Y) := by
    exact integrable_neg_iff.mp (hbase.1.congr he)
  refine ⟨hint, ?_⟩
  have hcomplex := hbase.2
  rw [integral_congr_ae he, integral_neg, neg_neg] at hcomplex
  have hre := congrArg Complex.re hcomplex
  have hreal := integral_re hint
  simp only [RCLike.re_to_complex] at hreal
  simpa only [Complex.sub_re] using hre.trans hreal.symm

theorem hardyPotential_interior_pinching_nonneg
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    (normalizedSpectralTrace hardyStripPotential
      ((ρ : ℂ) • B + Complex.I • positivePinchingPart B Y)).re ≤
      (normalizedSpectralTrace hardyStripPotential ((ρ : ℂ) • B + Complex.I • Y)).re := by
  apply sub_nonneg.mp
  rw [(hardyPotential_interior_pinching hB hB2 hY hρ).2]
  apply integral_nonneg_of_ae
  have hν : ∀ᵐ p ∂positivePinchingMeasure B Y,
      p ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y)) := by
    apply ae_iff.mpr
    exact positivePinching_measure_outside_rectangle hB hB2 hY
  exact hν.mono fun p hp => (hardyStripSecant_re_pos (strip_argument_mem hρ hp.1)).le

end
end CGLMPBounds.Hardy
