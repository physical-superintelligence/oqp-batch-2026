module

public import CGLMPBounds.Partition.AbelPairIntegralLimit

@[expose] public section


/-! Actual real paired-kernel integral on each ordered interval rectangle.
The singular complex limiting kernel is integrable by the genuine Abel
majorant, and Fubini gives exactly the iterated source integral. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory Filter
open scoped Topology
noncomputable section

lemma quarterBranch_limit_kernel_norm_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖-(scalarSecant x : ℂ) / 4 + Complex.I * (scalarSecant (1 - x) : ℂ) / 4‖ ≤
      1 / (2 * x) + 1 / (2 * (1 - x)) := by
  apply le_of_tendsto (quarterBranchAbelKernel_tendsto hx).norm
  have hlow : ∀ᶠ q : ℝ in 𝓝[<] (1 : ℝ), (1 / 2 : ℝ) < q :=
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hlow, self_mem_nhdsWithin] with q hq₀ hq₁
  exact quarterBranchAbelKernel_norm_le_endpoint_poles q hq₀.le hq₁ hx

lemma quarterBranch_limit_kernel_integrable
    {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hd : d ≤ 1) :
    Integrable (fun p : ℝ × ℝ =>
      -(scalarSecant (p.2 - p.1) : ℂ) / 4 +
        Complex.I * (scalarSecant (1 - (p.2 - p.1)) : ℂ) / 4)
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))) := by
  apply (pair_endpoint_poles_integrable_subrectangle ha hab hbc hcd hd).mono'
    (by unfold scalarSecant; fun_prop : Measurable _).aestronglyMeasurable
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  intro p hp
  have hx : p.2 - p.1 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  simpa only [show 1 - (p.2 - p.1) = 1 - p.2 + p.1 by ring] using
    quarterBranch_limit_kernel_norm_le hx

/-- The precise 1/2 and +Im signs in the actual iterated D.2 integral. -/
theorem quarterBranch_pair_kernel_rectangle_identity
    {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hd : d ≤ 1) (z : ℂ) :
    2 * ((∫ p : ℝ × ℝ,
      -(scalarSecant (p.2 - p.1) : ℂ) / 4 +
        Complex.I * (scalarSecant (1 - (p.2 - p.1)) : ℂ) / 4
      ∂((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d)))) * (star z - 1)).re =
      (1 / 2 : ℝ) * ∫ s in a..b, ∫ t in c..d,
        scalarSecant (t - s) * (1 - z.re) + scalarSecant (1 - t + s) * z.im := by
  let μ : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))
  let R : ℝ × ℝ → ℂ := fun p =>
    -(scalarSecant (p.2 - p.1) : ℂ) / 4 +
      Complex.I * (scalarSecant (1 - (p.2 - p.1)) : ℂ) / 4
  let P : ℝ × ℝ → ℝ := fun p =>
    scalarSecant (p.2 - p.1) * (1 - z.re) + scalarSecant (1 - p.2 + p.1) * z.im
  have hR : Integrable R μ := quarterBranch_limit_kernel_integrable ha hab hbc hcd hd
  have he (p : ℝ × ℝ) : 2 * (R p * (star z - 1)).re = (1 / 2 : ℝ) * P p := by
    simpa only [R, P, show 1 - (p.2 - p.1) = 1 - p.2 + p.1 by ring] using
      quarterBranch_pair_kernel_real (p.2 - p.1) z
  have hP : Integrable P μ := by
    apply ((hR.mul_const (star z - 1)).re.const_mul 4).congr
    filter_upwards [] with p
    have hh := he p
    simp only [RCLike.re_eq_complex_re]
    linarith
  have hiter : (∫ p, P p ∂μ) =
      ∫ s in a..b, ∫ t in c..d,
        scalarSecant (t - s) * (1 - z.re) + scalarSecant (1 - t + s) * z.im := by
    rw [integral_prod _ hP, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [] with s
    rw [intervalIntegral.integral_of_le hcd, integral_Ioc_eq_integral_Ioo]
  change 2 * ((∫ p, R p ∂μ) * (star z - 1)).re = _
  have hRe : (∫ p, (R p * (star z - 1)).re ∂μ) =
      (∫ p, R p * (star z - 1) ∂μ).re := by
    simpa only [RCLike.re_eq_complex_re] using integral_re (hR.mul_const (star z - 1))
  rw [← integral_mul_const, ← hRe, ← integral_const_mul]
  calc
    _ = ∫ p, (1 / 2 : ℝ) * P p ∂μ := integral_congr_ae (Filter.Eventually.of_forall he)
    _ = (1 / 2 : ℝ) * ∫ p, P p ∂μ := integral_const_mul _ _
    _ = _ := by rw [hiter]

end
end CGLMPBounds.Partition
