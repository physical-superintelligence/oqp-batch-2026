module

public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section


/-! Genuine integration over differences on the open unit triangle.
The factor 1-x is the actual length of the allowable origin interval.
Integrability and the change of variables are proved, not assumed. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
noncomputable section

theorem triangle_difference_integral (F : ℝ → ℝ)
    (hF : IntervalIntegrable F volume 0 1) :
    Integrable (fun p : ℝ × ℝ => if p.1 < p.2 then F (p.2 - p.1) else 0)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) ∧
    (∫ p : ℝ × ℝ, (if p.1 < p.2 then F (p.2 - p.1) else 0)
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) =
      ∫ x in (0 : ℝ)..1, (1 - x) * F x := by
  classical
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1
  let K : ℝ × ℝ → ℝ := S.indicator
    (fun p => if p.1 < p.2 then F (p.2 - p.1) else 0)
  let H : ℝ × ℝ → ℝ := fun p =>
    if 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1 then F p.2 else 0
  have hFi : Integrable ((Ioo (0 : ℝ) 1).indicator F) volume := by
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hF
  have h1i : Integrable ((Ioo (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact integrableOn_const (by simp : volume (Ioo (0 : ℝ) 1) ≠ ⊤)
  have hHeq : H = {p : ℝ × ℝ | p.1 + p.2 < 1}.indicator
      (fun p => (Ioo (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) p.1 *
        (Ioo (0 : ℝ) 1).indicator F p.2) := by
    funext p
    change (if 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1 then F p.2 else 0) = _
    by_cases h : 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1
    · have hs : p.1 ∈ Ioo (0 : ℝ) 1 := ⟨h.1, by linarith [h.2.1, h.2.2]⟩
      have ht : p.2 ∈ Ioo (0 : ℝ) 1 := ⟨h.2.1, by linarith [h.1, h.2.2]⟩
      rw [if_pos h, indicator_of_mem (s := {q : ℝ × ℝ | q.1 + q.2 < 1}) (a := p) h.2.2,
        indicator_of_mem hs,
        indicator_of_mem ht, one_mul]
    · rw [if_neg h]
      by_cases hp : p.1 + p.2 < 1
      · rw [indicator_of_mem (s := {q : ℝ × ℝ | q.1 + q.2 < 1}) (a := p) hp]
        by_cases hs : p.1 ∈ Ioo (0 : ℝ) 1
        · have ht : p.2 ∉ Ioo (0 : ℝ) 1 := fun ht => h ⟨hs.1, ht.1, hp⟩
          rw [indicator_of_notMem ht, mul_zero]
        · rw [indicator_of_notMem hs, zero_mul]
      · rw [indicator_of_notMem (s := {q : ℝ × ℝ | q.1 + q.2 < 1}) (a := p) hp]
  have hHi : Integrable H (volume.prod volume) := by
    rw [hHeq]
    exact (h1i.mul_prod hFi).indicator (by measurability)
  have hcomp : K ∘ (MeasurableEquiv.shearAddRight ℝ) = H := by
    funext p
    change K (p.1, p.1 + p.2) = H p
    by_cases h : 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1
    · have hs : (p.1, p.1 + p.2) ∈ S :=
        ⟨⟨h.1, by linarith [h.2.1, h.2.2]⟩,
          ⟨by linarith [h.1, h.2.1], h.2.2⟩⟩
      have hlt : p.1 < p.1 + p.2 := by linarith [h.2.1]
      simp [K, indicator_of_mem hs, hlt, H, h]
    · by_cases hs : (p.1, p.1 + p.2) ∈ S
      · have hn : ¬p.1 < p.1 + p.2 := by
          intro hlt
          exact h ⟨hs.1.1, by linarith, hs.2.2⟩
        simp [K, indicator_of_mem hs, hn, H, h]
      · simp [K, indicator_of_notMem hs, H, h]
  have hpres : MeasurePreserving (MeasurableEquiv.shearAddRight ℝ)
      (volume.prod volume) (volume.prod volume) := measurePreserving_prod_add volume volume
  have hKi : Integrable K (volume.prod volume) :=
    (hpres.integrable_comp_emb (MeasurableEquiv.shearAddRight ℝ).measurableEmbedding).mp
      (hcomp.symm ▸ hHi)
  have hHinner (x : ℝ) : (∫ s : ℝ, H (s, x)) =
      (Ioo (0 : ℝ) 1).indicator (fun x => (1 - x) * F x) x := by
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · have he : (fun s => H (s, x)) = (Ioo (0 : ℝ) (1 - x)).indicator (fun _ => F x) := by
        funext s
        by_cases hs : s ∈ Ioo (0 : ℝ) (1 - x)
        · have hp : 0 < s ∧ 0 < x ∧ s + x < 1 := ⟨hs.1, hx.1, by linarith [hs.2]⟩
          simp [H, hp, hs]
        · have hn : ¬(0 < s ∧ 0 < x ∧ s + x < 1) := by
            intro hp
            exact hs ⟨hp.1, by linarith [hp.2.2]⟩
          simp [H, hn, hs]
      rw [he, integral_indicator measurableSet_Ioo, setIntegral_const,
        indicator_of_mem hx]
      simp [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [hx.2] : 0 ≤ 1 - x),
        smul_eq_mul]
    · have he : (fun s => H (s, x)) = 0 := by
        funext s
        have hn : ¬(0 < s ∧ 0 < x ∧ s + x < 1) := by
          intro hp
          exact hx ⟨hp.2.1, by linarith [hp.1, hp.2.2]⟩
        simp [H, hn]
      simp [he, indicator_of_notMem hx]
  constructor
  · rw [Measure.prod_restrict]
    exact (integrable_indicator_iff (measurableSet_Ioo.prod measurableSet_Ioo)).mp hKi
  · rw [Measure.prod_restrict]
    change (∫ p in S, (if p.1 < p.2 then F (p.2 - p.1) else 0)) = _
    rw [← integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
    change (∫ p, K p ∂volume.prod volume) = _
    calc
      _ = ∫ p, H p ∂volume.prod volume := by
        rw [← hpres.integral_comp (MeasurableEquiv.shearAddRight ℝ).measurableEmbedding K]
        exact integral_congr_ae (Filter.Eventually.of_forall (congrFun hcomp))
      _ = ∫ x : ℝ, ∫ s : ℝ, H (s, x) := integral_prod_symm _ hHi
      _ = ∫ x : ℝ, (Ioo (0 : ℝ) 1).indicator (fun x => (1 - x) * F x) x := by
        apply integral_congr_ae; exact Filter.Eventually.of_forall hHinner
      _ = _ := by
        rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

end
end CGLMPBounds.Partition
