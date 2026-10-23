module

public import CGLMPBounds.Hardy.ContinuousGrowthVitali
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section


/-! The exact finite-measure L2-to-L1 boundary-passage interface for C.6.
The finite-measure Hölder factor is kept, including the zero-measure case. -/
namespace CGLMPBounds.Hardy
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

lemma tendsto_eLpNorm_one_of_two {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) [IsFiniteMeasure μ] (f : ℕ → α → E)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hlim : Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (nhds 0) := by
  let K : ℝ≥0∞ := μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hK : K ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)
  have hb := ENNReal.Tendsto.mul_const hlim (Or.inr hK)
  simp only [zero_mul] at hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => bot_le)
    (fun n => eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hf n))

/-- Generic continuous linear-growth composition from L2 to actual L1.
The closed range and continuity assumptions concern the original g, and both
conclusions assert genuine integrability before interpreting the integrals. -/
theorem continuousOn_linear_growth_L2_L1 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) [IsFiniteMeasure μ]
    (S : Set E) (hS : IsClosed S) (g : E → ℝ) (hg : ContinuousOn g S)
    (C : ℝ) (hC : 0 ≤ C) (hgrowth : ∀ x ∈ S, |g x| ≤ C * (1 + ‖x‖))
    (f : ℕ → α → E) (f₀ : α → E)
    (hf : ∀ n, MemLp (f n) 2 μ) (hf₀ : MemLp f₀ 2 μ)
    (hfS : ∀ n, ∀ᵐ x ∂μ, f n x ∈ S) (hf₀S : ∀ᵐ x ∂μ, f₀ x ∈ S)
    (hlim : Tendsto (fun n => eLpNorm (f n - f₀) 2 μ) atTop (nhds 0)) :
    (∀ n, Integrable (fun x => g (f n x)) μ) ∧
    Integrable (fun x => g (f₀ x)) μ ∧
    Tendsto (fun n => ∫ x, |g (f n x) - g (f₀ x)| ∂μ) atTop (nhds 0) := by
  have hf1 (n : ℕ) : MemLp (f n) 1 μ := (hf n).mono_exponent (by norm_num)
  have hf₀1 : MemLp f₀ 1 μ := hf₀.mono_exponent (by norm_num)
  have hlim1 := tendsto_eLpNorm_one_of_two μ (fun n => f n - f₀)
    (fun n => (hf n).aestronglyMeasurable.sub hf₀.aestronglyMeasurable) hlim
  have hgm (n : ℕ) : MemLp (fun x => g (f n x)) 1 μ :=
    continuousOn_linear_growth_memLp μ hS hg C hgrowth (hf1 n) (hfS n)
  have hgm₀ : MemLp (fun x => g (f₀ x)) 1 μ :=
    continuousOn_linear_growth_memLp μ hS hg C hgrowth hf₀1 hf₀S
  refine ⟨fun n => memLp_one_iff_integrable.mp (hgm n),
    memLp_one_iff_integrable.mp hgm₀, ?_⟩
  have h := continuousOn_linear_growth_tendsto_L1 μ S hS g hg C hC hgrowth
    f f₀ hf1 hf₀1 hfS hf₀S hlim1
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [ENNReal.toReal_zero] at hreal
  have heq (n : ℕ) :
      (eLpNorm (fun x => g (f n x) - g (f₀ x)) 1 μ).toReal =
        ∫ x, |g (f n x) - g (f₀ x)| ∂μ := by
    have hm : AEStronglyMeasurable (fun x => g (f n x) - g (f₀ x)) μ :=
      (hgm n).aestronglyMeasurable.sub hgm₀.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hm, ← integral_norm_eq_lintegral_enorm hm]
    simp only [Real.norm_eq_abs]
  simpa only [Function.comp_def, heq] using hreal

end
end CGLMPBounds.Hardy
