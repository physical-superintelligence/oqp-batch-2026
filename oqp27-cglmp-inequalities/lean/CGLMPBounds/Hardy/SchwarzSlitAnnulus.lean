module

public import CGLMPBounds.Hardy.SchwarzJoukowski
public import CGLMPBounds.Hardy.SchwarzAnnulusPole

@[expose] public section


/-!
# The actual regularized source kernel on Joukowski annuli

The literal pullback uses the derivative of J_a. Its numerator after removing
the unique exterior pole is an explicit rational expression in the actual
regularized source function. All analytic premises of the generic one-pole
annulus theorem are discharged from the source Hermitian-pencil hypotheses.

This gives a genuine contour identity before taking either radius to a limit.
The ellipse-to-bank limit is a separate remaining obligation.
-/

open Complex Matrix Filter Set Metric
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

lemma slitJoukowski_poleFactor_ne_zero {w s : ℂ}
    (hw : 1 < ‖w‖) (hs : 1 < ‖s‖) : 1 - (w * s)⁻¹ ≠ 0 := by
  have hprod : 1 < ‖w * s‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg w, norm_nonneg s]
  intro hf
  have hinv : (w * s)⁻¹ = 1 := (sub_eq_zero.mp hf).symm
  have hp : w * s = 1 := inv_eq_one.mp hinv
  rw [hp, norm_one] at hprod
  exact lt_irrefl _ hprod

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- Actual Cauchy kernel pulled back through the explicit ellipse map. -/
def slitPullbackKernel (H Y : Matrix ι ι ℂ) (a : ℝ) (s w : ℂ) : ℂ :=
  regularizedReflectedTrace H Y (slitJoukowski a w) /
    (slitJoukowski a w - slitJoukowski a s) * deriv (slitJoukowski a) w

/-- The explicit numerator after isolating the exterior simple pole w=s.
The second preimage 1/s is strictly inside the unit disk. -/
def slitPullbackNumerator (H Y : Matrix ι ι ℂ) (a : ℝ) (s w : ℂ) : ℂ :=
  regularizedReflectedTrace H Y (slitJoukowski a w) * (1 - (w ^ 2)⁻¹) /
    (1 - (w * s)⁻¹)

lemma slitPullbackNumerator_at_pole (H Y : Matrix ι ι ℂ) (a : ℝ)
    {s : ℂ} (hs : 1 < ‖s‖) :
    slitPullbackNumerator H Y a s s =
      regularizedReflectedTrace H Y (slitJoukowski a s) := by
  have hf := slitJoukowski_poleFactor_ne_zero hs hs
  unfold slitPullbackNumerator
  rw [pow_two]
  exact mul_div_cancel_right₀ _ hf

lemma slitPullbackKernel_eq_div (H Y : Matrix ι ι ℂ) {a : ℝ} (ha : 0 < a)
    {s w : ℂ} (hs : 1 < ‖s‖) (hw : 1 < ‖w‖) (hws : w ≠ s) :
    slitPullbackKernel H Y a s w = slitPullbackNumerator H Y a s w / (w - s) := by
  have hwn : w ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hw)
  have hsn : s ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hs)
  have hfac := slitJoukowski_poleFactor_ne_zero hw hs
  have hac : ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (div_pos ha (by norm_num)).ne'
  unfold slitPullbackKernel slitPullbackNumerator
  rw [(hasDerivAt_slitJoukowski a hwn).deriv, slitJoukowski_sub a hwn hsn]
  field_simp [hac, hfac, sub_ne_zero.mpr hws]
  <;> ring

theorem analyticOnNhd_slitPullbackNumerator
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {a : ℝ} (ha : 0 < a)
    (hYbound : |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)| ≤ a)
    {s : ℂ} (hs : 1 < ‖s‖) :
    AnalyticOnNhd ℂ (slitPullbackNumerator H Y a s) {w : ℂ | 1 < ‖w‖} := by
  intro w hw
  have hwn : w ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hw)
  have hsn : s ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hs)
  have hreg := analyticOnNhd_regularizedTrace_comp_slitJoukowski hH hY hdet ha hYbound w hw
  have hpow : AnalyticAt ℂ (fun v : ℂ => 1 - (v ^ 2)⁻¹) w :=
    analyticAt_const.sub ((analyticAt_id.pow 2).inv (pow_ne_zero 2 hwn))
  have hden : AnalyticAt ℂ (fun v : ℂ => 1 - (v * s)⁻¹) w :=
    analyticAt_const.sub ((analyticAt_id.mul analyticAt_const).inv (mul_ne_zero hwn hsn))
  exact (hreg.mul hpow).div hden (slitJoukowski_poleFactor_ne_zero hw hs)

/-- A genuine finite-annulus identity for the actual source kernel. There is
no extra analyticity, residue, boundary-limit, or moment assumption. Both
circles are positively oriented; the inner one is subtracted. -/
theorem slitPullbackKernel_annulus
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {a : ℝ} (ha : 0 < a)
    (hYbound : |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)| ≤ a)
    {s : ℂ} {r R : ℝ} (hr : 1 < r) (hrs : r < ‖s‖) (hsR : ‖s‖ < R) :
    (∮ w in C(0, R), slitPullbackKernel H Y a s w) -
      (∮ w in C(0, r), slitPullbackKernel H Y a s w) =
        (2 * Real.pi * Complex.I : ℂ) *
          regularizedReflectedTrace H Y (slitJoukowski a s) := by
  have hs : 1 < ‖s‖ := hr.trans hrs
  have hRp : 0 < R := (lt_trans zero_lt_one hs).trans hsR
  have hrp : 0 < r := lt_trans zero_lt_one hr
  have hf : AnalyticOnNhd ℂ (slitPullbackNumerator H Y a s)
      (closedBall 0 R \ ball 0 r) := by
    apply (analyticOnNhd_slitPullbackNumerator hH hY hdet ha hYbound hs).mono
    intro w hw
    have hn : r ≤ ‖w‖ := by
      simpa only [mem_ball, dist_zero_right, not_lt] using hw.2
    exact hr.trans_le hn
  have heqR : (∮ w in C(0, R), slitPullbackKernel H Y a s w) =
      ∮ w in C(0, R), slitPullbackNumerator H Y a s w / (w - s) := by
    apply circleIntegral.integral_congr hRp.le
    intro w hw
    have hn : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right] using hw
    apply slitPullbackKernel_eq_div H Y ha hs (by rw [hn]; exact hs.trans hsR)
    intro hws
    exact hsR.ne (hws ▸ hn)
  have heqr : (∮ w in C(0, r), slitPullbackKernel H Y a s w) =
      ∮ w in C(0, r), slitPullbackNumerator H Y a s w / (w - s) := by
    apply circleIntegral.integral_congr hrp.le
    intro w hw
    have hn : ‖w‖ = r := by simpa only [mem_sphere, dist_zero_right] using hw
    apply slitPullbackKernel_eq_div H Y ha hs (by rwa [hn])
    intro hws
    exact hrs.ne ((hws ▸ hn).symm)
  rw [heqR, heqr,
    circleIntegral_kernel_sub_eq_of_analyticOnNhd_annulus hrp hrs hsR hf,
    slitPullbackNumerator_at_pole H Y a hs]

end
end CGLMPBounds.Hardy
