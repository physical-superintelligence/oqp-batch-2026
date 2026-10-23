module

public import CGLMPBounds.Partition.PairPoleIntegrability
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section


/-! Dominated Abel limit on actual ordered interval rectangles. This
handles adjacent cells and both circle endpoint singularities. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory Filter
open scoped Topology
noncomputable section

lemma pair_endpoint_poles_integrable_subrectangle
    {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hd : d ≤ 1) :
    Integrable (fun p : ℝ × ℝ =>
      1 / (2 * (p.2 - p.1)) + 1 / (2 * (1 - p.2 + p.1)))
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))) := by
  have hb : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab, hbc.trans (hcd.trans hd)⟩
  have hbase := pair_endpoint_poles_integrable b hb
  rw [Measure.prod_restrict] at hbase ⊢
  apply IntegrableOn.mono_set hbase
  rintro p ⟨hs, ht⟩
  exact ⟨⟨ha.trans_lt hs.1, hs.2⟩, ⟨hbc.trans_lt ht.1, ht.2.trans_le hd⟩⟩

/-- The actual damped kernel integral converges on each ordered pair of
partition intervals, including adjacent intervals. -/
theorem quarterBranchAbelKernel_rectangle_tendsto
    {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hd : d ≤ 1) :
    Tendsto (fun q : ℝ =>
      ∫ p : ℝ × ℝ, quarterBranchAbelKernel q (p.2 - p.1)
        ∂((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ p : ℝ × ℝ,
        -(scalarSecant (p.2 - p.1) : ℂ) / 4 +
          Complex.I * (scalarSecant (1 - (p.2 - p.1)) : ℂ) / 4
        ∂((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))) := by
  let μ : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))
  have hmem : ∀ᵐ p : ℝ × ℝ ∂μ, p ∈ (Ioo a b ×ˢ Ioo c d) := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  have hgap (p : ℝ × ℝ) (hp : p ∈ (Ioo a b ×ˢ Ioo c d)) :
      p.2 - p.1 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hq : ∀ᶠ q : ℝ in 𝓝[<] (1 : ℝ), (1 / 2 : ℝ) < q ∧ q < 1 := by
    have hlow : ∀ᶠ q : ℝ in 𝓝[<] (1 : ℝ), (1 / 2 : ℝ) < q :=
      (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    exact hlow.and self_mem_nhdsWithin
  apply tendsto_integral_filter_of_dominated_convergence
    (fun p : ℝ × ℝ => 1 / (2 * (p.2 - p.1)) + 1 / (2 * (1 - p.2 + p.1)))
  · filter_upwards [hq] with q hqq
    have he : (fun p : ℝ × ℝ => quarterBranchAbelKernel q (p.2 - p.1)) =
        (fun p : ℝ × ℝ =>
          Complex.exp (((3 * Real.pi * (p.2 - p.1) / 2 : ℝ) : ℂ) * Complex.I) /
            (1 - (q : ℂ) * Complex.exp
              (((2 * Real.pi * (p.2 - p.1) : ℝ) : ℂ) * Complex.I))) := by
      funext p
      exact quarterBranchAbelKernel_eq q _ (by linarith [hqq.1]) hqq.2
    rw [he]
    exact (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [hq] with q hqq
    filter_upwards [hmem] with p hp
    simpa only [show 1 - (p.2 - p.1) = 1 - p.2 + p.1 by ring] using
      quarterBranchAbelKernel_norm_le_endpoint_poles q hqq.1.le hqq.2 (hgap p hp)
  · exact pair_endpoint_poles_integrable_subrectangle ha hab hbc hcd hd
  · filter_upwards [hmem] with p hp
    exact quarterBranchAbelKernel_tendsto (hgap p hp)

end
end CGLMPBounds.Partition
