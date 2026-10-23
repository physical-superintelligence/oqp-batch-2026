module

public import CGLMPBounds.Hardy.HardyPotentialSeriesIdentification

@[expose] public section


/-! The actual primitive is analytic at any point whose whole radial
segment avoids the secant poles. This includes both nonreal half-planes,
and identifies the actual values at x=±1,y≠0 without an endpoint oracle. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter
open scoped Topology

theorem analyticAt_segmentPrimitive {g : ℂ → ℂ} {z : ℂ}
    (hg : ∀ u ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ g ((u : ℂ) * z)) :
    AnalyticAt ℂ (segmentPrimitive g) z := by
  have he : ∀ᶠ w in 𝓝 z, ∀ u ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ g ((u : ℂ) * w) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    exact (by fun_prop : ContinuousAt (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) (z, u)).tendsto.eventually
      (hg u hu).eventually_analyticAt
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact he.mono fun w hw => (hasDerivAt_segmentPrimitive hw).differentiableAt

lemma hardyStrip_cos_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Complex.cos (Real.pi * z / 2) ≠ 0 := by
  intro hc
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
  have hi := congrArg Complex.im hk
  simp only [Complex.div_ofNat_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.one_im, Complex.add_re, Complex.add_im, zero_mul, mul_zero,
    add_zero, zero_add, zero_div] at hi
  apply hz
  nlinarith [Real.pi_pos]

lemma analyticAt_hardyStripSecant_nonreal {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ hardyStripSecant z :=
  analyticAt_const.div (Complex.analyticAt_cos.comp (by fun_prop))
    (hardyStrip_cos_ne_zero_of_im_ne_zero hz)

lemma analyticAt_hardyStripFirstPrimitive_nonreal {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ (segmentPrimitive hardyStripSecant) z := by
  apply analyticAt_segmentPrimitive
  intro u hu
  by_cases hu0 : u = 0
  · simpa only [hu0, Complex.ofReal_zero, zero_mul] using
      analyticOnNhd_hardyStripSecant 0 (by simp [openVerticalUnitStrip])
  · apply analyticAt_hardyStripSecant_nonreal
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using
      mul_ne_zero hu0 hz

theorem analyticAt_hardyStripPotential_nonreal {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ hardyStripPotential z := by
  apply analyticAt_const.sub (analyticAt_segmentPrimitive ?_)
  intro u hu
  by_cases hu0 : u = 0
  · simpa only [hu0, Complex.ofReal_zero, zero_mul] using
      (analyticOnNhd_segmentPrimitive analyticOnNhd_hardyStripSecant)
        0 (by simp [openVerticalUnitStrip])
  · apply analyticAt_hardyStripFirstPrimitive_nonreal
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using
      mul_ne_zero hu0 hz

theorem hardyStripPotential_eq_upper_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    hardyStripPotential z = hardyUpperPotential z := by
  have hh : AnalyticOnNhd ℂ hardyStripPotential {w : ℂ | 0 < w.im} :=
    fun w hw => analyticAt_hardyStripPotential_nonreal hw.ne'
  have hbase : (Complex.I / 2 : ℂ) ∈ openVerticalUnitStrip ∩ {w : ℂ | 0 < w.im} := by
    norm_num [openVerticalUnitStrip]
  have hS : IsOpen (openVerticalUnitStrip ∩ {w : ℂ | 0 < w.im}) :=
    (isOpen_lt Complex.continuous_re.abs continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have he : hardyStripPotential =ᶠ[𝓝 (Complex.I / 2)] hardyUpperPotential := by
    filter_upwards [hS.mem_nhds hbase] with w hw
    exact hardyStripPotential_eq_upper hw.1 hw.2
  exact hh.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_hardyUpperPotential
    (convex_halfSpace_im_gt 0).isPreconnected hbase.2 he hz

end
end CGLMPBounds.Hardy
