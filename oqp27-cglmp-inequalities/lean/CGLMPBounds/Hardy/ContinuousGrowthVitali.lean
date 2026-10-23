module

public import CGLMPBounds.Hardy.ContinuousGrowthIntegrability

@[expose] public section


/-! Continuous linear-growth composition is sequentially continuous in L1
on a closed almost-everywhere range. Uniform integrability is derived from
actual norm convergence, and the subsequence limit uses the actual continuous
function; there is no uniform-integrability or desired-limit premise. -/
namespace CGLMPBounds.Hardy
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

lemma continuousOn_linear_growth_tendsto_L1 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) [IsFiniteMeasure μ]
    (S : Set E) (hS : IsClosed S) (g : E → ℝ) (hg : ContinuousOn g S)
    (C : ℝ) (hC : 0 ≤ C) (hgrowth : ∀ x ∈ S, |g x| ≤ C * (1 + ‖x‖))
    (f : ℕ → α → E) (f₀ : α → E)
    (hf : ∀ n, MemLp (f n) 1 μ) (hf₀ : MemLp f₀ 1 μ)
    (hfS : ∀ n, ∀ᵐ x ∂μ, f n x ∈ S) (hf₀S : ∀ᵐ x ∂μ, f₀ x ∈ S)
    (hlim : Tendsto (fun n => eLpNorm (f n - f₀) 1 μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun x => g (f n x) - g (f₀ x)) 1 μ) atTop (nhds 0) := by
  let M : ℕ → α → ℝ := fun n x => C * (1 + ‖f n x‖)
  let M₀ : α → ℝ := fun x => C * (1 + ‖f₀ x‖)
  have hM (n : ℕ) : MemLp (M n) 1 μ :=
    ((memLp_const (1 : ℝ)).add (hf n).norm).const_mul C
  have hM₀ : MemLp M₀ 1 μ :=
    ((memLp_const (1 : ℝ)).add hf₀.norm).const_mul C
  have hMlim : Tendsto (fun n => eLpNorm (M n - M₀) 1 μ) atTop (nhds 0) := by
    have hb := ENNReal.Tendsto.const_mul hlim (Or.inr (by finiteness : ‖C‖ₑ ≠ ⊤))
    simp only [mul_zero] at hb
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun _ => bot_le)
      (fun n => linear_growth_majorant_difference_eLpNorm_le 1 C hC
        (hf n).aestronglyMeasurable hf₀.aestronglyMeasurable)
  have hMui := unifIntegrable_of_tendsto_Lp (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hM hM₀ hMlim
  have hgm (n : ℕ) : MemLp (fun x => g (f n x)) 1 μ :=
    continuousOn_linear_growth_memLp μ hS hg C hgrowth (hf n) (hfS n)
  have hgm₀ : MemLp (fun x => g (f₀ x)) 1 μ :=
    continuousOn_linear_growth_memLp μ hS hg C hgrowth hf₀ hf₀S
  have hgui : UnifIntegrable (fun n x => g (f n x)) 1 μ := by
    apply hMui.ae_mono (fun n => (hgm n).aestronglyMeasurable)
    intro n
    filter_upwards [hfS n] with x hx
    have h : ‖g (f n x)‖ ≤ ‖M n x‖ := by
      have hMn : 0 ≤ M n x := mul_nonneg hC (by positivity)
      change |g (f n x)| ≤ |M n x|
      rw [abs_of_nonneg hMn]
      exact hgrowth (f n x) hx
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal h
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (1 : ℝ≥0∞) ≠ 0) hlim
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hmslim⟩ := (hmeasure.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    (fun n => (hgm (ns (ms n))).aestronglyMeasurable) hgm₀
    (hgui.comp (fun n => ns (ms n)))
  have hall : ∀ᵐ x ∂μ, ∀ n, f n x ∈ S := ae_all_iff.mpr hfS
  filter_upwards [hmslim, hall, hf₀S] with x hx hxS hx₀
  exact (hg (f₀ x) hx₀).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hx, Filter.Eventually.of_forall (fun n => hxS _)⟩)

end
end CGLMPBounds.Hardy
