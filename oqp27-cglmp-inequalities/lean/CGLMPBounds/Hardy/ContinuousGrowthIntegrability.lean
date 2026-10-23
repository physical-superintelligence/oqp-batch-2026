module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Topology.TietzeExtension

@[expose] public section


/-! A continuous real function on a closed set with linear growth preserves
finite-measure Lp membership. Tietze is used only for measurability; the
norm estimate uses the given function on the actual almost-everywhere range. -/
namespace CGLMPBounds.Hardy
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

lemma continuousOn_comp_aestronglyMeasurable {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {S : Set E} (hS : IsClosed S) {g : E → ℝ} (hg : ContinuousOn g S)
    {f : α → E} (hf : AEStronglyMeasurable f μ) (hfS : ∀ᵐ x ∂μ, f x ∈ S) :
    AEStronglyMeasurable (fun x => g (f x)) μ := by
  let gS : C(S, ℝ) := ⟨S.domRestrict g, hg.domRestrict⟩
  obtain ⟨G, hG⟩ := gS.exists_restrict_eq hS
  have heq : ∀ x ∈ S, G x = g x := by
    intro x hx
    exact congrArg (fun H : C(S, ℝ) => H ⟨x, hx⟩) hG
  exact (G.continuous.comp_aestronglyMeasurable hf).congr
    (hfS.mono (fun x hx => heq (f x) hx))

lemma continuousOn_linear_growth_memLp {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) [IsFiniteMeasure μ] {p : ℝ≥0∞}
    {S : Set E} (hS : IsClosed S) {g : E → ℝ} (hg : ContinuousOn g S)
    (C : ℝ) (hgrowth : ∀ x ∈ S, |g x| ≤ C * (1 + ‖x‖))
    {f : α → E} (hf : MemLp f p μ) (hfS : ∀ᵐ x ∂μ, f x ∈ S) :
    MemLp (fun x => g (f x)) p μ := by
  have hm : MemLp (fun x => C * (1 + ‖f x‖)) p μ :=
    ((memLp_const (1 : ℝ)).add hf.norm).const_mul C
  apply hm.mono' (continuousOn_comp_aestronglyMeasurable hS hg hf.aestronglyMeasurable hfS)
  filter_upwards [hfS] with x hx
  exact hgrowth (f x) hx

lemma linear_growth_majorant_difference_eLpNorm_le {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    (p : ℝ≥0∞) (C : ℝ) (hC : 0 ≤ C) {f f₀ : α → E}
    (hf : AEStronglyMeasurable f μ) (hf₀ : AEStronglyMeasurable f₀ μ) :
    eLpNorm (fun x => C * (1 + ‖f x‖) - C * (1 + ‖f₀ x‖)) p μ ≤
      ‖C‖ₑ * eLpNorm (f - f₀) p μ := by
  have hbound : ∀ x,
      ‖C * (1 + ‖f x‖) - C * (1 + ‖f₀ x‖)‖ ≤
        ‖C * ‖f x - f₀ x‖‖ := by
    intro x
    rw [show C * (1 + ‖f x‖) - C * (1 + ‖f₀ x‖) =
      C * (‖f x‖ - ‖f₀ x‖) by ring]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC, abs_norm]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le (f x) (f₀ x)) hC
  have hm := eLpNorm_mono_ae
    ((hf.norm.const_add 1).const_mul C |>.sub ((hf₀.norm.const_add 1).const_mul C))
    (Filter.Eventually.of_forall hbound) (p := p)
  calc
    _ ≤ eLpNorm (C • (fun x => ‖(f - f₀) x‖)) p μ := hm
    _ = _ := by rw [eLpNorm_const_smul, eLpNorm_norm _ (hf.sub hf₀)]

end
end CGLMPBounds.Hardy
