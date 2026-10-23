module

public import CGLMPBounds.Hardy.HardyPotentialSeriesDerivative
public import CGLMPBounds.Hardy.HardyPotentialAnalytic
public import CGLMPBounds.Hardy.SecondDerivativeUniqueness

@[expose] public section


/-! Identification of the actual double primitive with the convergent
upper half-plane series. Both boundary initial data are proved along the
positive imaginary axis, then analytic uniqueness determines the function.
This does not identify values of the double integral at strip endpoints. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter
open scoped Topology

lemma analyticOnNhd_hardyUpperPotential :
    AnalyticOnNhd ℂ hardyUpperPotential {z : ℂ | 0 < z.im} := by
  intro z hz
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
  exact (hasDerivAt_hardyUpperPotential hw).differentiableAt

lemma hardyUpperPotential_imaginary_derivative {y : ℝ} (hy : 0 < y) :
    deriv hardyUpperPotential (Complex.I * y) =
      -Complex.I + (4 * Complex.I / Real.pi) *
        (Real.arctan (Real.exp (-Real.pi * y / 2)) : ℂ) := by
  rw [(hasDerivAt_hardyUpperPotential (z := Complex.I * y) (by simpa using hy)).deriv]
  have ha : Complex.I * Real.pi * (Complex.I * y) / 2 =
      ((-Real.pi * y / 2 : ℝ) : ℂ) := by
    push_cast
    calc
      _ = Complex.I ^ 2 * (Real.pi : ℂ) * y / 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [ha, ← Complex.ofReal_exp, ← Complex.ofReal_arctan]

theorem hardyStripPotential_eq_upper {z : ℂ}
    (hz : z ∈ openVerticalUnitStrip) (hy : 0 < z.im) :
    hardyStripPotential z = hardyUpperPotential z := by
  let S : Set ℂ := openVerticalUnitStrip ∩ {z : ℂ | 0 < z.im}
  have hS : IsOpen S := (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hcS : IsPreconnected S := by
    have hs : S = ({z : ℂ | -(1 : ℝ) < z.re} ∩ {z : ℂ | z.re < 1}) ∩
        {z : ℂ | 0 < z.im} := by
      ext w
      simp only [S, mem_inter_iff, openVerticalUnitStrip, mem_setOf_eq, abs_lt]
    rw [hs]
    exact (((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_re_lt 1)).inter
      (convex_halfSpace_im_gt 0)).isPreconnected
  let γ : ℝ → ℂ := fun y => Complex.I * y
  have hγ : ∀ᶠ y in 𝓝[>] (0 : ℝ), γ y ∈ S := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    constructor
    · simp [γ, openVerticalUnitStrip]
    · simpa [γ] using hy
  have hγ0 : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hc : Continuous γ := by dsimp [γ]; fun_prop
    simpa only [γ, Complex.ofReal_zero, mul_zero] using
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hγclosed : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝[{w : ℂ | 0 ≤ w.im}] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hγ0, ?_⟩
    filter_upwards [hγ] with y hy
    exact (show 0 < (γ y).im from hy.2).le
  have huvalue : Tendsto (fun y => hardyUpperPotential (γ y)) (𝓝[>] (0 : ℝ))
      (𝓝 (hardyStripCenterConstant : ℂ)) := by
    have h := (continuousOn_hardyUpperPotential.continuousWithinAt
      (show (0 : ℂ) ∈ {w : ℂ | 0 ≤ w.im} by simp)).tendsto.comp hγclosed
    simpa only [Function.comp_def, hardyUpperPotential_zero] using h
  have hzero : (0 : ℂ) ∈ openVerticalUnitStrip := by simp [openVerticalUnitStrip]
  have hhvalue : Tendsto (fun y => hardyStripPotential (γ y)) (𝓝[>] (0 : ℝ))
      (𝓝 (hardyStripCenterConstant : ℂ)) := by
    have h := (analyticOnNhd_hardyStripPotential 0 hzero).continuousAt.tendsto.comp hγ0
    simpa only [Function.comp_def, hardyStripPotential_initial_and_differential_data.2.1] using h
  have hud : Tendsto (fun y => deriv hardyUpperPotential (γ y)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun y : ℝ => -Complex.I + (4 * Complex.I / Real.pi) *
        (Real.arctan (Real.exp (-Real.pi * y / 2)) : ℂ)) := by fun_prop
    have heval : -Complex.I + (4 * Complex.I / Real.pi) *
        (Real.arctan (Real.exp (-Real.pi * (0 : ℝ) / 2)) : ℂ) = 0 := by
      simp only [mul_zero, zero_div, Real.exp_zero, Real.arctan_one,
        Complex.ofReal_div, Complex.ofReal_ofNat]
      field_simp [Real.pi_ne_zero] <;> ring
    have hl := (hc.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rw [heval] at hl
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hardyUpperPotential_imaginary_derivative hy).symm
  have hhd : Tendsto (fun y => deriv hardyStripPotential (γ y)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (analyticOnNhd_hardyStripPotential 0 hzero).deriv.continuousAt.tendsto.comp hγ0
    simpa only [Function.comp_def, hardyStripPotential_initial_and_differential_data.2.2.1] using h
  have he := analytic_eqOn_of_second_derivative_boundary_limits hS hcS
    (analyticOnNhd_hardyUpperPotential.mono inter_subset_right)
    (analyticOnNhd_hardyStripPotential.mono inter_subset_left)
    (fun w hw => (hardyUpperPotential_second_derivative hw.2).trans
      (hardyStripPotential_second_derivative hw.1).symm)
    γ hγ huvalue hhvalue hud hhd
  exact (he ⟨hz, hy⟩).symm

end
end CGLMPBounds.Hardy
