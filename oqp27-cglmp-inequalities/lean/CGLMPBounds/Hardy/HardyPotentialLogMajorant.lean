module

public import CGLMPBounds.Hardy.HardyPotentialBoundsInterior
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section


/-! An integrable logarithmic majorant for the actual first radial primitive.
It controls the defining outer integral even at the two real strip corners;
the inner primitive's exceptional endpoint value is a null-set issue. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology

lemma hardyStrip_cos_re_ge {z : ℂ} (hz : |z.re| ≤ 1) :
    1 - |z.re| ≤ (Complex.cos (Real.pi * z / 2)).re := by
  have hp := Real.pi_pos
  have hb := Real.one_sub_mul_le_cos
    (x := Real.pi * |z.re| / 2) (by positivity) (by nlinarith)
  have he : 2 / Real.pi * (Real.pi * |z.re| / 2) = |z.re| := by
    field_simp
  rw [he] at hb
  have hcos : Real.cos (Real.pi * |z.re| / 2) = Real.cos (Real.pi * z.re / 2) := by
    calc
      _ = Real.cos |Real.pi * z.re / 2| := by
        congr 1
        rw [abs_div, abs_mul, abs_of_pos hp]
        norm_num
      _ = _ := Real.cos_abs _
  rw [hcos] at hb
  rw [real_part_complex_cos]
  simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  exact hb.trans (le_mul_of_one_le_right (by linarith : 0 ≤ Real.cos (Real.pi*z.re/2))
    (Real.one_le_cosh _))

lemma hardyStripSecant_norm_le_radial {z : ℂ} (hz : |z.re| ≤ 1)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    ‖hardyStripSecant ((t : ℂ)*z)‖ ≤ 1 / (1-t) := by
  have hre : |((t : ℂ)*z).re| ≤ t := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, abs_mul, abs_of_nonneg ht.1, mul_one] using mul_le_mul_of_nonneg_left hz ht.1
  have hb := hardyStrip_cos_re_ge (hre.trans ht.2.le)
  have hn : 1-t ≤ ‖Complex.cos (Real.pi*((t : ℂ)*z)/2)‖ :=
    (by linarith : 1-t ≤ (Complex.cos (Real.pi*((t : ℂ)*z)/2)).re).trans
      (Complex.re_le_norm _)
  rw [hardyStripSecant, norm_div, norm_one]
  exact one_div_le_one_div_of_le (sub_pos.mpr ht.2) hn

lemma segmentPrimitive_radial_interval (g : ℂ → ℂ) (z : ℂ) (u : ℝ) :
    segmentPrimitive g ((u : ℂ)*z) = z * ∫ t in (0 : ℝ)..u, g ((t : ℂ)*z) := by
  have he : (u : ℂ) * (∫ v in (0 : ℝ)..1, g (((v*u : ℝ) : ℂ)*z)) =
      ∫ t in (0 : ℝ)..u, g ((t : ℂ)*z) := by
    simpa only [zero_mul, one_mul, Complex.real_smul] using
      (intervalIntegral.smul_integral_comp_mul_right
        (fun t : ℝ => g ((t : ℂ)*z)) u (a := 0) (b := 1))
  unfold segmentPrimitive
  rw [← he]
  have hi : (∫ v in (0 : ℝ)..1, g ((v : ℂ)*((u : ℂ)*z))) =
      ∫ v in (0 : ℝ)..1, g (((v*u : ℝ) : ℂ)*z) := by
    apply intervalIntegral.integral_congr
    intro v hv
    simp only [Complex.ofReal_mul, mul_assoc]
  rw [hi]
  ring

lemma hardy_log_majorant_integrable :
    IntervalIntegrable (fun u : ℝ => -Real.log (1-u)) volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).comp_sub_left 1
  have hh : IntervalIntegrable (fun u : ℝ => Real.log (1-u)) volume 0 1 := by
    simpa only [sub_self, sub_zero] using h.symm
  exact ⟨hh.1.fun_neg, hh.2.fun_neg⟩

lemma hardy_log_majorant_nonneg {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    0 ≤ -Real.log (1-u) := by
  exact neg_nonneg.mpr (Real.log_nonpos (sub_nonneg.mpr hu.2.le) (sub_le_self 1 hu.1))

lemma hardy_reciprocal_integral {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..u, 1/(1-t)) = -Real.log (1-u) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => 1/t) 1,
    sub_zero, integral_one_div_of_pos (sub_pos.mpr hu.2) zero_lt_one]
  simp only [one_div, Real.log_inv]

theorem hardyStripFirstPrimitive_log_majorant {z : ℂ} (hz : |z.re| ≤ 1)
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    ‖segmentPrimitive hardyStripSecant ((u : ℂ)*z)‖ ≤
      ‖z‖ * (-Real.log (1-u)) := by
  rw [segmentPrimitive_radial_interval, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
  rw [← hardy_reciprocal_integral hu]
  apply intervalIntegral.norm_integral_le_of_norm_le hu.1
  · exact Filter.Eventually.of_forall fun t ht =>
      hardyStripSecant_norm_le_radial hz ⟨ht.1.le, ht.2.trans_lt hu.2⟩
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_const.sub continuousOn_id)
    intro t ht
    rw [uIcc_of_le hu.1] at ht
    change 1 - t ≠ 0
    exact (sub_pos.mpr (ht.2.trans_lt hu.2)).ne'

end
end CGLMPBounds.Hardy
