module

public import CGLMPBounds.Partition.AbelKernelBound
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section


/-! Genuine integrability of the two endpoint poles across a partition
boundary. AM–GM bounds a reciprocal sum by a product of inverse square
roots; each factor is integrable by Mathlib's rpow theorem. This supplies
the domination needed for D.2 without assuming the desired pair identity. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
noncomputable section

lemma reciprocal_add_le_rpow_product {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    1 / (u + v) ≤ (1 / 2 : ℝ) *
      (u ^ (-(1 / 2 : ℝ)) * v ^ (-(1 / 2 : ℝ))) := by
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hamgm : 2 * Real.sqrt u * Real.sqrt v ≤ u + v := by
    nlinarith [sq_nonneg (Real.sqrt u - Real.sqrt v),
      Real.sq_sqrt hu.le, Real.sq_sqrt hv.le]
  rw [Real.rpow_neg hu.le, Real.rpow_neg hv.le,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  calc
    _ ≤ 1 / (2 * Real.sqrt u * Real.sqrt v) :=
      one_div_le_one_div_of_le (by positivity) hamgm
    _ = _ := by field_simp <;> ring

lemma pair_endpoint_poles_le_majorant {b s t : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) b) (ht : t ∈ Ioo b 1) :
    1 / (2 * (t - s)) + 1 / (2 * (1 - t + s)) ≤
      (1 / 4 : ℝ) *
        ((b - s) ^ (-(1 / 2 : ℝ)) * (t - b) ^ (-(1 / 2 : ℝ)) +
          s ^ (-(1 / 2 : ℝ)) * (1 - t) ^ (-(1 / 2 : ℝ))) := by
  have h₁ := reciprocal_add_le_rpow_product
    (show 0 < b - s by linarith [hs.2]) (show 0 < t - b by linarith [ht.1])
  have h₂ := reciprocal_add_le_rpow_product hs.1 (show 0 < 1 - t by linarith [ht.2])
  rw [show b - s + (t - b) = t - s by ring] at h₁
  rw [show s + (1 - t) = 1 - t + s by ring] at h₂
  have he₁ : 1 / (2 * (t - s)) = (1 / 2 : ℝ) * (1 / (t - s)) := by
    rw [one_div_mul_one_div]
  have he₂ : 1 / (2 * (1 - t + s)) = (1 / 2 : ℝ) * (1 / (1 - t + s)) := by
    rw [one_div_mul_one_div]
  rw [he₁, he₂]
  linarith

lemma pair_endpoint_majorant_integrable (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p : ℝ × ℝ => (1 / 4 : ℝ) *
      ((b - p.1) ^ (-(1 / 2 : ℝ)) * (p.2 - b) ^ (-(1 / 2 : ℝ)) +
        p.1 ^ (-(1 / 2 : ℝ)) * (1 - p.2) ^ (-(1 / 2 : ℝ))))
      ((volume.restrict (Ioo (0 : ℝ) b)).prod (volume.restrict (Ioo b 1))) := by
  have hpow (a c : ℝ) : IntervalIntegrable
      (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume a c :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h₁ : IntegrableOn (fun s : ℝ => (b - s) ^ (-(1 / 2 : ℝ))) (Ioo 0 b) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.1).mp
    simpa using ((hpow 0 b).comp_sub_left b).symm
  have h₂ : IntegrableOn (fun t : ℝ => (t - b) ^ (-(1 / 2 : ℝ))) (Ioo b 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2).mp
    simpa using (hpow 0 (1 - b)).comp_sub_right b
  have h₃ : IntegrableOn (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) (Ioo 0 b) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.1).mp (hpow 0 b)
  have h₄ : IntegrableOn (fun t : ℝ => (1 - t) ^ (-(1 / 2 : ℝ))) (Ioo b 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2).mp
    simpa using ((hpow 0 (1 - b)).comp_sub_left 1).symm
  exact ((h₁.mul_prod h₂).add (h₃.mul_prod h₄)).const_mul (1 / 4 : ℝ)

/-- Both singularities are genuinely integrable on opposite sides of any
boundary. End boundaries yield empty rectangles, as they should. -/
theorem pair_endpoint_poles_integrable (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p : ℝ × ℝ =>
      1 / (2 * (p.2 - p.1)) + 1 / (2 * (1 - p.2 + p.1)))
      ((volume.restrict (Ioo (0 : ℝ) b)).prod (volume.restrict (Ioo b 1))) := by
  apply (pair_endpoint_majorant_integrable b hb).mono'
    (show AEStronglyMeasurable (fun p : ℝ × ℝ =>
      1 / (2 * (p.2 - p.1)) + 1 / (2 * (1 - p.2 + p.1))) _ from
      (by fun_prop : Measurable _).aestronglyMeasurable)
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  intro p hp
  have hx : 0 < p.2 - p.1 := by linarith [hp.1.2, hp.2.1]
  have hy : 0 < 1 - p.2 + p.1 := by linarith [hp.1.1, hp.2.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pair_endpoint_poles_le_majorant hp.1 hp.2

end
end CGLMPBounds.Partition
