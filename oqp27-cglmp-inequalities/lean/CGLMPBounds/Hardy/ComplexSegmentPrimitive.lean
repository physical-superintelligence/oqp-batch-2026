module

public import CGLMPBounds.Defs.HardyPotential
public import CGLMPBounds.Hardy.CompactParametricIntegral

@[expose] public section


/-! Genuine straight-segment primitives of holomorphic functions on a
star-shaped domain. Differentiation is justified by compact parameter
integration; the primitive identity follows from the ordinary interval
fundamental theorem of calculus, not from a primitive oracle. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

theorem hasDerivAt_intervalIntegral_joint_analytic
    {F : ℂ × ℂ → ℂ} {z : ℂ}
    (hF : ∀ u ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ F (z, (u : ℂ))) :
    HasDerivAt (fun w => ∫ u : ℝ in (0 : ℝ)..1, F (w, (u : ℂ)))
      (∫ u : ℝ in (0 : ℝ)..1, deriv (fun w => F (w, (u : ℂ))) z) z := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let μ : Measure ℂ := ν.map Complex.ofReal
  let K : Set ℂ := Complex.ofReal '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hμK : ∀ᵐ a ∂μ, a ∈ K := by
    apply (ae_map_iff Complex.continuous_ofReal.measurable.aemeasurable hK.measurableSet).mpr
    exact (ae_restrict_mem measurableSet_Icc).mono fun u hu => mem_image_of_mem _ hu
  have hr : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem hμK
  have hmap (g : ℂ → ℂ) (hg : ContinuousOn g K) :
      (∫ a in K, g a ∂μ) = ∫ u : ℝ in (0 : ℝ)..1, g (u : ℂ) := by
    have hm : AEStronglyMeasurable g μ := by
      simpa only [hr] using hg.aestronglyMeasurable (μ := μ) hK.measurableSet
    rw [hr, integral_map Complex.continuous_ofReal.measurable.aemeasurable hm,
      intervalIntegral.integral_of_le zero_le_one, restrict_Ioc_eq_restrict_Icc]
  have hF0 : ∀ a ∈ K, AnalyticAt ℂ F (z, a) := by
    rintro a ⟨u, hu, rfl⟩
    exact hF u hu
  have he : ∀ᶠ w in 𝓝 z, ∀ a ∈ K, AnalyticAt ℂ F (w, a) :=
    hK.eventually_forall_of_forall_eventually
      (fun a ha => (hF0 a ha).eventually_analyticAt)
  have hd := hasDerivAt_integral_compact_joint_analytic hK μ he
  have hvalue : (fun w => ∫ a in K, F (w, a) ∂μ) =ᶠ[𝓝 z]
      (fun w => ∫ u : ℝ in (0 : ℝ)..1, F (w, (u : ℂ))) := by
    filter_upwards [he] with w hw
    exact hmap _ (continuousOn_compact_analytic_slice hw)
  have hD : ContinuousOn (circleParameterDerivative F z) K := by
    intro a ha
    exact ((continuousAt_circleParameterDerivative (hF0 a ha)).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hderiv : (∫ a in K, circleParameterDerivative F z a ∂μ) =
      ∫ u : ℝ in (0 : ℝ)..1, deriv (fun w => F (w, (u : ℂ))) z := by
    rw [hmap _ hD]
    apply intervalIntegral.integral_congr
    intro u hu
    exact (hasDerivAt_circleSlice (hF u (by simpa using hu))).deriv.symm
  rw [hderiv] at hd
  exact hd.congr_of_eventuallyEq hvalue.symm

theorem hasDerivAt_segmentPrimitive {g : ℂ → ℂ} {z : ℂ}
    (hg : ∀ u ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ g ((u : ℂ) * z)) :
    HasDerivAt (segmentPrimitive g) (g z) z := by
  let F : ℂ × ℂ → ℂ := fun p => g (p.2 * p.1)
  have hF : ∀ u ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ F (z, (u : ℂ)) := by
    intro u hu
    exact (hg u hu).comp (f := fun p : ℂ × ℂ => p.2 * p.1)
      (analyticAt_snd.mul analyticAt_fst)
  have hd := hasDerivAt_intervalIntegral_joint_analytic hF
  have hslice (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      deriv (fun w => F (w, (u : ℂ))) z = (u : ℂ) * deriv g ((u : ℂ) * z) := by
    exact (((hg u hu).differentiableAt.hasDerivAt).comp z
      ((hasDerivAt_id z).const_mul (u : ℂ))).deriv.trans (by ring)
  have hc : ContinuousOn (fun u : ℝ => g ((u : ℂ) * z) +
      (u : ℂ) * z * deriv g ((u : ℂ) * z)) (Icc (0 : ℝ) 1) := by
    intro u hu
    exact (((hg u hu).continuousAt.comp (f := fun v : ℝ => (v : ℂ) * z)
      (by fun_prop)).add
      ((by fun_prop : ContinuousAt (fun u : ℝ => (u : ℂ) * z) u).mul
        ((hg u hu).deriv.continuousAt.comp (f := fun v : ℝ => (v : ℂ) * z)
          (by fun_prop)))).continuousWithinAt
  have hFTC : (∫ u : ℝ in (0 : ℝ)..1,
      g ((u : ℂ) * z) + (u : ℂ) * z * deriv g ((u : ℂ) * z)) = g z := by
    have hder (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) 1) :
        HasDerivAt (fun v : ℝ => (v : ℂ) * g ((v : ℂ) * z))
          (g ((u : ℂ) * z) + (u : ℂ) * z * deriv g ((u : ℂ) * z)) u := by
      have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
      have h : HasDerivAt (fun v : ℂ => v * g (v * z))
          (g ((u : ℂ) * z) + (u : ℂ) * (deriv g ((u : ℂ) * z) * z)) (u : ℂ) := by
        simpa only [Pi.mul_apply, Function.comp_apply, id_eq, one_mul] using!
          (hasDerivAt_id (u : ℂ)).mul
            (((hg u hu').differentiableAt.hasDerivAt).comp (u : ℂ)
              ((hasDerivAt_id (u : ℂ)).mul_const z))
      exact (h.congr_deriv (by ring)).comp_ofReal
    have hci : ContinuousOn (fun u : ℝ => g ((u : ℂ) * z) +
        (u : ℂ) * z * deriv g ((u : ℂ) * z)) (uIcc (0 : ℝ) 1) := by
      simpa only [uIcc_of_le zero_le_one] using hc
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hder hci.intervalIntegrable
  have hi₀ : IntervalIntegrable (fun u : ℝ => g ((u : ℂ) * z)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    exact ((hg u (by simpa using hu)).continuousAt.comp
      (f := fun v : ℝ => (v : ℂ) * z) (by fun_prop)).continuousWithinAt
  have hi₁ : IntervalIntegrable (fun u : ℝ => (u : ℂ) * z * deriv g ((u : ℂ) * z))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    exact ((by fun_prop : ContinuousAt (fun u : ℝ => (u : ℂ) * z) u).mul
      ((hg u (by simpa using hu)).deriv.continuousAt.comp
        (f := fun v : ℝ => (v : ℂ) * z) (by fun_prop))).continuousWithinAt
  have hcoef : (∫ u : ℝ in (0 : ℝ)..1, F (z, (u : ℂ))) + z *
      (∫ u : ℝ in (0 : ℝ)..1, deriv (fun w => F (w, (u : ℂ))) z) = g z := by
    rw [← hFTC, intervalIntegral.integral_add hi₀ hi₁,
      ← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    change z * deriv (fun w => F (w, (u : ℂ))) z =
      (u : ℂ) * z * deriv g ((u : ℂ) * z)
    rw [hslice u (by simpa using hu)]
    ring
  convert (hasDerivAt_id z).mul hd using 1
  · rfl
  · simpa only [one_mul, id_eq] using hcoef.symm

theorem analyticOnNhd_segmentPrimitive {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g openVerticalUnitStrip) :
    AnalyticOnNhd ℂ (segmentPrimitive g) openVerticalUnitStrip := by
  have hS : IsOpen openVerticalUnitStrip := isOpen_lt Complex.continuous_re.abs continuous_const
  have hseg {z : ℂ} (hz : z ∈ openVerticalUnitStrip) {u : ℝ}
      (hu : u ∈ Icc (0 : ℝ) 1) : (u : ℂ) * z ∈ openVerticalUnitStrip := by
    change |((u : ℂ) * z).re| < 1
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, abs_mul,
      abs_of_nonneg hu.1]
    exact (mul_le_of_le_one_left (abs_nonneg z.re) hu.2).trans_lt hz
  intro z hz
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [hS.mem_nhds hz] with w hw
  exact (hasDerivAt_segmentPrimitive (fun u hu => hg _ (hseg hw hu))).differentiableAt

end
end CGLMPBounds.Hardy
