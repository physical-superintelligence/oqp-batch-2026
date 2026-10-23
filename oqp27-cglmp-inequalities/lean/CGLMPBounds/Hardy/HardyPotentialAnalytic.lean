module

public import CGLMPBounds.Hardy.ComplexSegmentPrimitive

@[expose] public section


/-! The actual C.14 scalar potential satisfies the printed initial data
and differential equation. The real part of its negative second derivative
is strictly positive in the open strip. Boundary statements remain separate. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter
open scoped Topology

lemma real_part_complex_cos (z : ℂ) :
    (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
  rw [Complex.cos_eq]
  simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re]

lemma hardyStrip_cos_re_pos {z : ℂ} (hz : z ∈ openVerticalUnitStrip) :
    0 < (Complex.cos (Real.pi * z / 2)).re := by
  rw [real_part_complex_cos]
  apply mul_pos
  · apply Real.cos_pos_of_mem_Ioo
    have hb := abs_lt.mp (show |z.re| < 1 from hz)
    simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    constructor <;> nlinarith [Real.pi_pos]
  · exact Real.cosh_pos _

lemma hardyStrip_cos_ne_zero {z : ℂ} (hz : z ∈ openVerticalUnitStrip) :
    Complex.cos (Real.pi * z / 2) ≠ 0 := by
  intro he
  have hp := hardyStrip_cos_re_pos hz
  simpa only [he, Complex.zero_re, lt_self_iff_false] using hp

theorem analyticOnNhd_hardyStripSecant :
    AnalyticOnNhd ℂ hardyStripSecant openVerticalUnitStrip := by
  intro z hz
  exact analyticAt_const.div (Complex.analyticAt_cos.comp (by fun_prop))
    (hardyStrip_cos_ne_zero hz)

theorem hardyStripSecant_re_pos {z : ℂ} (hz : z ∈ openVerticalUnitStrip) :
    0 < (hardyStripSecant z).re := by
  rw [hardyStripSecant, one_div, Complex.inv_re]
  exact div_pos (hardyStrip_cos_re_pos hz)
    (Complex.normSq_pos.mpr (hardyStrip_cos_ne_zero hz))

lemma real_segment_mem_openVerticalUnitStrip {z : ℂ}
    (hz : z ∈ openVerticalUnitStrip) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (u : ℂ) * z ∈ openVerticalUnitStrip := by
  change |((u : ℂ) * z).re| < 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, abs_mul, abs_of_nonneg hu.1]
  exact (mul_le_of_le_one_left (abs_nonneg z.re) hu.2).trans_lt hz

theorem hasDerivAt_hardyStripFirstPrimitive {z : ℂ}
    (hz : z ∈ openVerticalUnitStrip) :
    HasDerivAt (segmentPrimitive hardyStripSecant) (hardyStripSecant z) z :=
  hasDerivAt_segmentPrimitive (fun u hu =>
    analyticOnNhd_hardyStripSecant _ (real_segment_mem_openVerticalUnitStrip hz hu))

theorem analyticOnNhd_hardyStripPotential :
    AnalyticOnNhd ℂ hardyStripPotential openVerticalUnitStrip :=
  analyticOnNhd_const.sub (analyticOnNhd_segmentPrimitive
    (analyticOnNhd_segmentPrimitive analyticOnNhd_hardyStripSecant))

theorem hasDerivAt_hardyStripPotential {z : ℂ} (hz : z ∈ openVerticalUnitStrip) :
    HasDerivAt hardyStripPotential (-segmentPrimitive hardyStripSecant z) z := by
  have hp := analyticOnNhd_segmentPrimitive analyticOnNhd_hardyStripSecant
  simpa only [hardyStripPotential, Pi.sub_apply, zero_sub] using!
    (hasDerivAt_const z (hardyStripCenterConstant : ℂ)).sub
    (hasDerivAt_segmentPrimitive (fun u hu => hp _
      (real_segment_mem_openVerticalUnitStrip hz hu)))

theorem hardyStripPotential_second_derivative {z : ℂ} (hz : z ∈ openVerticalUnitStrip) :
    iteratedDeriv 2 hardyStripPotential z = -hardyStripSecant z := by
  have hS : IsOpen openVerticalUnitStrip := isOpen_lt Complex.continuous_re.abs continuous_const
  have he : deriv hardyStripPotential =ᶠ[𝓝 z]
      (fun w => -segmentPrimitive hardyStripSecant w) := by
    filter_upwards [hS.mem_nhds hz] with w hw
    exact (hasDerivAt_hardyStripPotential hw).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, he.deriv_eq]
  exact (hasDerivAt_hardyStripFirstPrimitive hz).neg.deriv

theorem hardyStripPotential_initial_and_differential_data :
    AnalyticOnNhd ℂ hardyStripPotential openVerticalUnitStrip ∧
    hardyStripPotential 0 = (hardyStripCenterConstant : ℂ) ∧
    deriv hardyStripPotential 0 = 0 ∧
    ∀ z ∈ openVerticalUnitStrip, iteratedDeriv 2 hardyStripPotential z = -hardyStripSecant z := by
  refine ⟨analyticOnNhd_hardyStripPotential, ?_, ?_, fun _ hz => hardyStripPotential_second_derivative hz⟩
  · simp [hardyStripPotential, segmentPrimitive]
  · rw [(hasDerivAt_hardyStripPotential (z := 0) (by simp [openVerticalUnitStrip])).deriv]
    simp [segmentPrimitive]

end
end CGLMPBounds.Hardy
