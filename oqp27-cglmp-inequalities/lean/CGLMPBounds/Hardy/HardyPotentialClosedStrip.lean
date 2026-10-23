module

public import CGLMPBounds.Hardy.HardyPotentialLogMajorant

@[expose] public section


/-! Continuity of the actual defining double integral on the closed strip.
The logarithmic bound proves dominated convergence even at z=±1. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology Interval

lemma radial_closed_strip_mem_open {z : ℂ} (hz : |z.re| ≤ 1)
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    (u : ℂ)*z ∈ openVerticalUnitStrip := by
  change |((u : ℂ)*z).re| < 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, abs_mul, abs_of_nonneg hu.1]
  exact (mul_le_mul_of_nonneg_left hz hu.1).trans_lt (by simpa using hu.2)

lemma hardyStripFirstPrimitive_radial_measurable {z : ℂ} (hz : |z.re| ≤ 1) :
    AEStronglyMeasurable (fun u : ℝ => segmentPrimitive hardyStripSecant ((u : ℂ)*z))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hc : ContinuousOn (fun u : ℝ => segmentPrimitive hardyStripSecant ((u : ℂ)*z))
      (Ioo (0 : ℝ) 1) := by
    intro u hu
    exact (((analyticOnNhd_segmentPrimitive analyticOnNhd_hardyStripSecant)
      _ (radial_closed_strip_mem_open hz ⟨hu.1.le, hu.2⟩)).continuousAt.comp
      (f := fun v : ℝ => (v : ℂ)*z) (x := u)
      (show ContinuousAt (fun v : ℝ => (v : ℂ)*z) u by fun_prop)).continuousWithinAt
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := 1))]
  exact hc.aestronglyMeasurable measurableSet_Ioo

theorem continuousOn_hardyStripPotential_closed :
    ContinuousOn hardyStripPotential {z : ℂ | |z.re| ≤ 1} := by
  intro z hz
  let M : ℝ := ‖z‖ + 1
  have hnorm : ∀ᶠ w in 𝓝[{z : ℂ | |z.re| ≤ 1}] z, ‖w‖ ≤ M :=
    ((continuous_norm.continuousAt.eventually_lt continuousAt_const
      (by dsimp [M]; linarith : ‖z‖ < M)).filter_mono nhdsWithin_le_nhds).mono
      fun w hw => hw.le
  have hmeas : ∀ᶠ w in 𝓝[{z : ℂ | |z.re| ≤ 1}] z,
      AEStronglyMeasurable (fun u : ℝ => segmentPrimitive hardyStripSecant ((u : ℂ)*w))
        (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    simpa only [uIoc_of_le zero_le_one] using hardyStripFirstPrimitive_radial_measurable hw
  have hbound : ∀ᶠ w in 𝓝[{z : ℂ | |z.re| ≤ 1}] z,
      ∀ᵐ (u : ℝ) ∂volume, u ∈ Ι (0 : ℝ) 1 →
        ‖segmentPrimitive hardyStripSecant ((u : ℂ)*w)‖ ≤ M*(-Real.log (1-u)) := by
    filter_upwards [self_mem_nhdsWithin, hnorm] with w hw hn
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with u hu
    intro hum
    rw [uIoc_of_le zero_le_one] at hum
    have hus : u ∈ Ico (0 : ℝ) 1 := ⟨hum.1.le, lt_of_le_of_ne hum.2 hu⟩
    exact (hardyStripFirstPrimitive_log_majorant hw hus).trans
      (mul_le_mul_of_nonneg_right hn (hardy_log_majorant_nonneg hus))
  have hcont : ∀ᵐ (u : ℝ) ∂volume, u ∈ Ι (0 : ℝ) 1 →
      ContinuousWithinAt (fun w : ℂ => segmentPrimitive hardyStripSecant ((u : ℂ)*w))
        {z : ℂ | |z.re| ≤ 1} z := by
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with u hu
    intro hum
    rw [uIoc_of_le zero_le_one] at hum
    exact (((analyticOnNhd_segmentPrimitive analyticOnNhd_hardyStripSecant)
      _ (radial_closed_strip_mem_open hz ⟨hum.1.le, lt_of_le_of_ne hum.2 hu⟩)).continuousAt.comp
      (f := fun w : ℂ => (u : ℂ)*w) (x := z)
      (show ContinuousAt (fun w : ℂ => (u : ℂ)*w) z by fun_prop)).continuousWithinAt
  have hi := intervalIntegral.continuousWithinAt_of_dominated_interval hmeas hbound
    (hardy_log_majorant_integrable.const_mul M) hcont
  exact continuousWithinAt_const.sub (continuousWithinAt_id.mul hi)

theorem continuousOn_hardyStripPotential_re_closed :
    ContinuousOn (fun z : ℂ => (hardyStripPotential z).re) {z : ℂ | |z.re| ≤ 1} :=
  Complex.continuous_re.comp_continuousOn continuousOn_hardyStripPotential_closed

lemma continuous_hardyStripRealPotential_vertical_closed {x : ℝ} (hx : |x| ≤ 1) :
    Continuous (fun y : ℝ => hardyStripRealPotential x y) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hz : |((x : ℂ)+Complex.I*y).re| ≤ 1 := by simpa using hx
  have hp : Tendsto (fun v : ℝ => (x : ℂ)+Complex.I*v) (𝓝 y)
      (𝓝[{z : ℂ | |z.re| ≤ 1}] ((x : ℂ)+Complex.I*y)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(show ContinuousAt (fun v : ℝ => (x : ℂ)+Complex.I*v) y by fun_prop), ?_⟩
    exact Filter.Eventually.of_forall fun v => by simpa using hx
  exact Complex.continuous_re.continuousAt.tendsto.comp
    ((continuousOn_hardyStripPotential_closed _ hz).tendsto.comp hp)

theorem hardyStripRealPotential_boundary (y : ℝ) :
    hardyStripRealPotential 1 y = |y| ∧ hardyStripRealPotential (-1) y = |y| := by
  by_cases hy : y = 0
  · subst y
    have hl := (continuous_hardyStripRealPotential_vertical_closed
      (x := 1) (by norm_num)).continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    have he : (fun v : ℝ => hardyStripRealPotential 1 v) =ᶠ[𝓝[>] (0 : ℝ)] id := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact (hardyStripRealPotential_boundary_nonzero v (ne_of_gt hv)).1.trans (abs_of_pos hv)
    have hzero : hardyStripRealPotential 1 0 = 0 :=
      tendsto_nhds_unique hl (tendsto_id.mono_left nhdsWithin_le_nhds |>.congr' he.symm)
    refine ⟨by simpa using hzero, ?_⟩
    simpa only [hardyStripRealPotential_even_x, abs_zero] using hzero
  · exact hardyStripRealPotential_boundary_nonzero y hy

theorem hardyStripRealPotential_bounds {x y : ℝ} (hx : |x| ≤ 1) :
    0 ≤ hardyStripRealPotential x y ∧
      hardyStripRealPotential x y ≤ hardyStripCenterConstant + |y| := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact hardyStripRealPotential_bounds_interior hlt
  · have hx' : x = 1 ∨ x = -1 := by
      by_cases hx0 : 0 ≤ x
      · left
        simpa only [abs_of_nonneg hx0] using heq
      · right
        rw [abs_of_neg (lt_of_not_ge hx0)] at heq
        linarith
    have hu : hardyStripRealPotential x y = |y| := by
      rcases hx' with rfl | rfl
      · exact (hardyStripRealPotential_boundary y).1
      · exact (hardyStripRealPotential_boundary y).2
    have hc : 0 ≤ hardyStripCenterConstant := by
      have h := (hardyStripRealPotential_bounds_interior (x := 0) (y := 0) (by norm_num)).1
      simpa [hardyStripRealPotential, hardyStripPotential, segmentPrimitive] using h
    rw [hu]
    exact ⟨abs_nonneg y, le_add_of_nonneg_left hc⟩

end
end CGLMPBounds.Hardy
