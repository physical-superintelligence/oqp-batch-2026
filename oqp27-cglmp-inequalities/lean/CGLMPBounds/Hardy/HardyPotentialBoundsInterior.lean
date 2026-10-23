module

public import CGLMPBounds.Hardy.HardyPotentialConcavity

@[expose] public section


/-! C.14 bounds for the actual potential away from its two real corners.
The axis estimate is an actual derivative estimate, and the real interior
line is recovered by continuity of the actual double primitive. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter Complex
open scoped Topology

lemma hasDerivAt_realPart_vertical {f : ℂ → ℂ} {f' : ℂ} (y : ℝ)
    (hf : HasDerivAt f f' (Complex.I * y)) :
    HasDerivAt (fun v : ℝ => (f (Complex.I * v)).re) (f' * Complex.I).re y := by
  have hc : HasDerivAt (fun z : ℂ => f (Complex.I * z))
      (f' * Complex.I) (y : ℂ) := by
    simpa only [mul_one, Function.comp_def, id_eq] using
      hf.comp (y : ℂ) ((hasDerivAt_id (y : ℂ)).const_mul Complex.I)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hc.comp_ofReal

lemma hardyStripRealPotential_axis_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun v : ℝ => hardyStripRealPotential 0 v)
      (1 - 4 / Real.pi * Real.arctan (Real.exp (-Real.pi * y / 2))) y := by
  have he : hardyStripPotential =ᶠ[𝓝 (Complex.I * y)] hardyUpperPotential := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (show (0 : ℝ) < (Complex.I * y).im by simpa using hy)] with w hw
    exact hardyStripPotential_eq_upper_of_im_pos hw
  have hu := (hasDerivAt_hardyUpperPotential (z := Complex.I * y) (by simpa using hy))
  have hu' := hu.differentiableAt.hasDerivAt
  rw [hardyUpperPotential_imaginary_derivative hy] at hu'
  have hh := hasDerivAt_realPart_vertical y (hu'.congr_of_eventuallyEq he)
  convert hh using 1
  · simp [hardyStripRealPotential]
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.div_ofReal_re, Complex.div_ofReal_im]
    ring

lemma continuous_hardyStripRealPotential_axis :
    Continuous (fun y : ℝ => hardyStripRealPotential 0 y) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hz : Complex.I * y ∈ openVerticalUnitStrip := by simp [openVerticalUnitStrip]
  simpa only [hardyStripRealPotential, Complex.ofReal_zero, zero_add, Function.comp_def] using
    Complex.continuous_re.continuousAt.comp
      ((analyticOnNhd_hardyStripPotential _ hz).continuousAt.comp
        (f := fun v : ℝ => Complex.I * v) (x := y) (by fun_prop))

theorem hardyStripRealPotential_axis_upper (y : ℝ) :
    hardyStripRealPotential 0 y ≤ hardyStripCenterConstant + |y| := by
  have hpos (v : ℝ) (hv : 0 ≤ v) :
      hardyStripRealPotential 0 v ≤ hardyStripCenterConstant + v := by
    have hd (w : ℝ) (hw : w ∈ interior (Icc (0 : ℝ) v)) :=
      hardyStripRealPotential_axis_hasDerivAt
        (show w ∈ Ioo (0 : ℝ) v by simpa only [interior_Icc] using hw).1
    have h := (convex_Icc (0 : ℝ) v).image_sub_le_mul_sub_of_deriv_le
      continuous_hardyStripRealPotential_axis.continuousOn
      (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
      (C := 1) (fun w hw => by
        rw [(hd w hw).deriv]
        have ha := Real.arctan_nonneg.mpr (Real.exp_pos (-Real.pi*w/2)).le
        have hc : 0 ≤ 4 / Real.pi * Real.arctan (Real.exp (-Real.pi*w/2)) :=
          mul_nonneg (by positivity) ha
        linarith)
      0 (by exact ⟨le_rfl, hv⟩) v (by exact ⟨hv, le_rfl⟩) hv
    have hzero : hardyStripRealPotential 0 0 = hardyStripCenterConstant := by
      simp [hardyStripRealPotential, hardyStripPotential, segmentPrimitive]
    rw [hzero] at h
    linarith
  by_cases hy : 0 ≤ y
  · simpa only [abs_of_nonneg hy] using hpos y hy
  · have h := hpos (-y) (by linarith)
    rw [hardyStripRealPotential_even_y] at h
    simpa only [abs_of_neg (lt_of_not_ge hy)] using h

theorem hardyStripRealPotential_bounds_nonreal {x y : ℝ}
    (hx : |x| ≤ 1) (hy : y ≠ 0) :
    0 ≤ hardyStripRealPotential x y ∧
      hardyStripRealPotential x y ≤ hardyStripCenterConstant + |y| := by
  have hb := hardyStripRealPotential_endpoint_center_bounds hx hy
  exact ⟨(abs_nonneg y).trans hb.1, hb.2.trans (hardyStripRealPotential_axis_upper y)⟩

theorem hardyStripRealPotential_bounds_interior {x y : ℝ} (hx : |x| < 1) :
    0 ≤ hardyStripRealPotential x y ∧
      hardyStripRealPotential x y ≤ hardyStripCenterConstant + |y| := by
  by_cases hy : y = 0
  · subst y
    have hz : (x : ℂ) ∈ openVerticalUnitStrip := by simpa [openVerticalUnitStrip] using hx
    have hc : ContinuousAt (fun v : ℝ => hardyStripRealPotential x v) 0 := by
      exact Complex.continuous_re.continuousAt.comp
        ((analyticOnNhd_hardyStripPotential _ hz).continuousAt.comp_of_eq
          (f := fun v : ℝ => (x : ℂ) + Complex.I * v) (x := (0 : ℝ))
          (by fun_prop) (by simp))
    have hlim := hc.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    have hb : ∀ᶠ v in 𝓝[>] (0 : ℝ),
        0 ≤ hardyStripRealPotential x v ∧
        hardyStripRealPotential x v ≤ hardyStripCenterConstant + |v| := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact hardyStripRealPotential_bounds_nonreal hx.le (ne_of_gt hv)
    refine ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hlim (hb.mono fun _ h => h.1), ?_⟩
    have hc' : Tendsto (fun v : ℝ => hardyStripCenterConstant + |v|)
        (𝓝[>] (0 : ℝ)) (𝓝 (hardyStripCenterConstant + |(0 : ℝ)|)) :=
      (show ContinuousAt (fun v : ℝ => hardyStripCenterConstant + |v|) 0 by fun_prop).tendsto.mono_left
        nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hlim hc' (hb.mono fun _ h => h.2)
  · exact hardyStripRealPotential_bounds_nonreal hx.le hy

end
end CGLMPBounds.Hardy
