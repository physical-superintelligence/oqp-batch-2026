module

public import CGLMPBounds.Partition.PairPoleIntegrability
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section


/-! A uniform L1 bound for the two endpoint poles across any boundary.
This bound is independent of the boundary location and hence can be
integrated against arbitrary finite boundary distributions. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
noncomputable section

private lemma integral_inv_sqrt_zero {b : ℝ} (hb : 0 ≤ b) :
    (∫ x in (0 : ℝ)..b, x ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt b := by
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring,
    Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero]
  rw [← Real.sqrt_eq_rpow]
  ring

theorem pair_endpoint_poles_integral_le_two (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ p : ℝ × ℝ,
      1 / (2 * (p.2 - p.1)) + 1 / (2 * (1 - p.2 + p.1))
      ∂((volume.restrict (Ioo (0 : ℝ) b)).prod (volume.restrict (Ioo b 1)))) ≤ 2 := by
  let μ : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioo (0 : ℝ) b)).prod (volume.restrict (Ioo b 1))
  let M : ℝ × ℝ → ℝ := fun p => (1 / 4 : ℝ) *
    ((b - p.1) ^ (-(1 / 2 : ℝ)) * (p.2 - b) ^ (-(1 / 2 : ℝ)) +
      p.1 ^ (-(1 / 2 : ℝ)) * (1 - p.2) ^ (-(1 / 2 : ℝ)))
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
  have i₁ : (∫ s in Ioo (0 : ℝ) b, (b - s) ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt b := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb.1]
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) b]
    simpa using integral_inv_sqrt_zero hb.1
  have i₂ : (∫ t in Ioo b (1 : ℝ), (t - b) ^ (-(1 / 2 : ℝ))) =
      2 * Real.sqrt (1 - b) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb.2]
    rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) b]
    simpa using integral_inv_sqrt_zero (show 0 ≤ 1 - b by linarith [hb.2])
  have i₃ : (∫ s in Ioo (0 : ℝ) b, s ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt b := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb.1]
    exact integral_inv_sqrt_zero hb.1
  have i₄ : (∫ t in Ioo b (1 : ℝ), (1 - t) ^ (-(1 / 2 : ℝ))) =
      2 * Real.sqrt (1 - b) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb.2]
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) 1]
    simpa using integral_inv_sqrt_zero (show 0 ≤ 1 - b by linarith [hb.2])
  have hMint : (∫ p, M p ∂μ) = 2 * Real.sqrt b * Real.sqrt (1 - b) := by
    dsimp only [M, μ]
    rw [integral_const_mul, integral_add (h₁.mul_prod h₂) (h₃.mul_prod h₄),
      integral_prod_mul (fun s : ℝ => (b - s) ^ (-(1 / 2 : ℝ)))
        (fun t : ℝ => (t - b) ^ (-(1 / 2 : ℝ))),
      integral_prod_mul (fun s : ℝ => s ^ (-(1 / 2 : ℝ)))
        (fun t : ℝ => (1 - t) ^ (-(1 / 2 : ℝ))), i₁, i₂, i₃, i₄]
    ring
  have hMbound : (∫ p, M p ∂μ) ≤ 2 := by
    rw [hMint]
    have hs₁ : Real.sqrt b ≤ 1 := (Real.sqrt_le_one).mpr hb.2
    have hs₂ : Real.sqrt (1 - b) ≤ 1 := (Real.sqrt_le_one).mpr (by linarith [hb.1])
    have hp := mul_le_mul hs₁ hs₂ (Real.sqrt_nonneg _) zero_le_one
    nlinarith
  refine le_trans ?_ hMbound
  apply integral_mono_ae (pair_endpoint_poles_integrable b hb) (pair_endpoint_majorant_integrable b hb)
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  intro p hp
  exact pair_endpoint_poles_le_majorant hp.1 hp.2

end
end CGLMPBounds.Partition
