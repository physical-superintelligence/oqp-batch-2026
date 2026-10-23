module

public import CGLMPBounds.Hardy.SchwarzOuterCircle
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section


/-!
# A concrete analytic coordinate for shrinking slit contours

J_a(w)=(a/2)(w+w⁻¹) maps the exterior unit disk injectively into the complement
of [-a,a]. Its concentric circles are ellipses that can approach the two banks.
The map and all derivatives below are actual rational functions; no contour
deformation or integral identity is included among the hypotheses.

These are auxiliary calculus ingredients for the remaining C.8 proof, not new
source definitions of g, q, or the density.
-/

open Complex Matrix Filter Set Metric
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

def slitJoukowski (a : ℝ) (w : ℂ) : ℂ :=
  ((a / 2 : ℝ) : ℂ) * (w + w⁻¹)

lemma slitJoukowski_neg (a : ℝ) (w : ℂ) :
    slitJoukowski a (-w) = -slitJoukowski a w := by
  simp only [slitJoukowski, inv_neg]
  ring

lemma slitJoukowski_ofReal (a x : ℝ) :
    slitJoukowski a (x : ℂ) = ((a / 2 * (x + x⁻¹) : ℝ) : ℂ) := by
  simp [slitJoukowski]

lemma slitJoukowski_im (a : ℝ) (w : ℂ) :
    (slitJoukowski a w).im = (a / 2) * (1 - 1 / Complex.normSq w) * w.im := by
  simp only [slitJoukowski, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.inv_im, zero_mul, add_zero]
  ring

lemma slitJoukowski_im_factor_pos {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 1 < ‖w‖) :
    0 < (a / 2) * (1 - 1 / Complex.normSq w) := by
  have hn : 1 < Complex.normSq w := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hnp : 0 < Complex.normSq w := lt_trans zero_lt_one hn
  exact mul_pos (div_pos ha (by norm_num))
    (sub_pos.mpr ((div_lt_one hnp).mpr hn))

lemma slitJoukowski_im_pos_iff {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 1 < ‖w‖) :
    0 < (slitJoukowski a w).im ↔ 0 < w.im := by
  rw [slitJoukowski_im]
  exact mul_pos_iff_of_pos_left (slitJoukowski_im_factor_pos ha hw)

lemma slitJoukowski_im_eq_zero_iff {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 1 < ‖w‖) :
    (slitJoukowski a w).im = 0 ↔ w.im = 0 := by
  rw [slitJoukowski_im, mul_eq_zero]
  simp only [(slitJoukowski_im_factor_pos ha hw).ne', false_or]

lemma slitJoukowski_real_gt {a x : ℝ} (ha : 0 < a) (hx : 1 < x) :
    a < (slitJoukowski a (x : ℂ)).re := by
  have hxp : 0 < x := lt_trans zero_lt_one hx
  have hmul : x * 2 < x * (x + x⁻¹) := by
    rw [mul_add, mul_inv_cancel₀ hxp.ne']
    nlinarith [sq_pos_of_pos (sub_pos.mpr hx)]
  have hsum : 2 < x + x⁻¹ := (mul_lt_mul_iff_right₀ hxp).mp hmul
  rw [slitJoukowski_ofReal, Complex.ofReal_re]
  nlinarith

/-- Real images of exterior-unit points lie strictly outside the whole
centered segment, not merely off the source's smaller spectral interval. -/
lemma slitJoukowski_real_outside {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 1 < ‖w‖)
    (him : (slitJoukowski a w).im = 0) :
    a < |(slitJoukowski a w).re| := by
  have hwi : w.im = 0 := (slitJoukowski_im_eq_zero_iff ha hw).mp him
  have hwe : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hwi]
  have hwr : 1 < |w.re| := by
    calc 1 < ‖w‖ := hw
         _ = |w.re| := by rw [hwe, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  rcases lt_abs.mp hwr with hp | hn
  · have hh := (slitJoukowski_real_gt ha hp).trans_le (le_abs_self _)
    rwa [← hwe] at hh
  · have hp : 1 < -w.re := by linarith
    have hh := slitJoukowski_real_gt ha hp
    rw [Complex.ofReal_neg, slitJoukowski_neg, Complex.neg_re, ← hwe] at hh
    exact hh.trans_le (neg_le_abs _)

lemma hasDerivAt_slitJoukowski (a : ℝ) {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (slitJoukowski a) (((a / 2 : ℝ) : ℂ) * (1 - (w ^ 2)⁻¹)) w := by
  change HasDerivAt (fun z : ℂ => ((a / 2 : ℝ) : ℂ) * (z + z⁻¹)) _ w
  simpa only [sub_eq_add_neg, id_eq] using
    ((hasDerivAt_id w).fun_add (hasDerivAt_inv hw)).const_mul ((a / 2 : ℝ) : ℂ)

lemma analyticAt_slitJoukowski (a : ℝ) {w : ℂ} (hw : w ≠ 0) :
    AnalyticAt ℂ (slitJoukowski a) w := by
  exact analyticAt_const.mul (analyticAt_id.add (analyticAt_inv hw))

/-- Exact two-preimage factorization, used to isolate a genuine simple pole. -/
lemma slitJoukowski_sub (a : ℝ) {w s : ℂ} (hw : w ≠ 0) (hs : s ≠ 0) :
    slitJoukowski a w - slitJoukowski a s =
      ((a / 2 : ℝ) : ℂ) * (w - s) * (1 - (w * s)⁻¹) := by
  unfold slitJoukowski
  field_simp [hw, hs] <;> ring

lemma slitJoukowski_injOn {a : ℝ} (ha : 0 < a) :
    Set.InjOn (slitJoukowski a) {w : ℂ | 1 < ‖w‖} := by
  intro w hw s hs he
  change 1 < ‖w‖ at hw
  change 1 < ‖s‖ at hs
  have hwn : w ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hw)
  have hsn : s ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hs)
  have hprod : 1 < ‖w * s‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg w, norm_nonneg s]
  have hfac : 1 - (w * s)⁻¹ ≠ 0 := by
    intro hf
    have hinv : (w * s)⁻¹ = 1 := (sub_eq_zero.mp hf).symm
    have hp : w * s = 1 := inv_eq_one.mp hinv
    rw [hp, norm_one] at hprod
    exact (lt_irrefl _ hprod)
  have hc : ((a / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos ha (by norm_num)).ne'
  have hz := slitJoukowski_sub a hwn hsn
  rw [he, sub_self] at hz
  have hm := mul_eq_zero.mp hz.symm
  rcases hm with hm | hm
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hc)
  · exact (hfac hm).elim

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma slitJoukowski_not_mem_spectralSlit (Y : Matrix ι ι ℂ) {a : ℝ} (ha : 0 < a)
    (hYbound : |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)| ≤ a)
    {w : ℂ} (hw : 1 < ‖w‖) : slitJoukowski a w ∉ spectralSlit Y := by
  intro hmem
  have hout := slitJoukowski_real_outside ha hw hmem.1
  have hb := spectralSlit_subset_closedBall Y hmem
  have hnorm : ‖slitJoukowski a w‖ ≤ a :=
    (by simpa only [mem_closedBall, dist_zero_right] using hb :
      ‖slitJoukowski a w‖ ≤ |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)|).trans hYbound
  exact (not_le.mpr hout) ((Complex.abs_re_le_norm _).trans hnorm)

/-- The actual regularized source function composed with this explicit
coordinate is holomorphic on the exterior unit disk. -/
theorem analyticOnNhd_regularizedTrace_comp_slitJoukowski
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {a : ℝ} (ha : 0 < a)
    (hYbound : |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)| ≤ a) :
    AnalyticOnNhd ℂ (fun w => regularizedReflectedTrace H Y (slitJoukowski a w))
      {w : ℂ | 1 < ‖w‖} := by
  intro w hw
  exact (analyticOnNhd_regularizedReflectedTrace hH hY hdet _
    (slitJoukowski_not_mem_spectralSlit Y ha hYbound hw)).comp
      (analyticAt_slitJoukowski a (norm_pos_iff.mp (lt_trans zero_lt_one hw)))

end
end CGLMPBounds.Hardy
