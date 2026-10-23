module

public import CGLMPBounds.Hardy.SchwarzSlitAnnulus

@[expose] public section


/-!
# Vanishing of the outer Joukowski contour

The Joukowski coordinate tends to complex infinity. The actual pole-removed
numerator therefore tends to zero, since the source remainder does and its
rational prefactor tends to one. A direct circle norm estimate then makes the
outer pullback integral vanish. No ellipse-bank limit is assumed here.
-/

open Complex Matrix Filter Set Metric Bornology
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

lemma slitJoukowski_norm_lower {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 1 ≤ ‖w‖) :
    (a / 2) * (‖w‖ - 1) ≤ ‖slitJoukowski a w‖ := by
  have hi : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hw
  have hsum : ‖w‖ - ‖w⁻¹‖ ≤ ‖w + w⁻¹‖ := by
    simpa only [norm_neg, sub_neg_eq_add] using norm_sub_norm_le w (-w⁻¹)
  rw [slitJoukowski, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos ha (by norm_num))]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

lemma tendsto_slitJoukowski_cobounded {a : ℝ} (ha : 0 < a) :
    Tendsto (slitJoukowski a) (cobounded ℂ) (cobounded ℂ) := by
  apply tendsto_norm_atTop_iff_cobounded.mp
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) (max 1 (2 * b / a + 1))]
    with w hw
  have hw1 : 1 ≤ ‖w‖ := (le_max_left _ _).trans hw
  have hb : 2 * b ≤ (‖w‖ - 1) * a :=
    (div_le_iff₀ ha).mp (by have := (le_max_right _ _).trans hw; linarith)
  exact (by nlinarith : b ≤ (a / 2) * (‖w‖ - 1)).trans
    (slitJoukowski_norm_lower ha hw1)

/-- A vanishing numerator has a vanishing large-circle Cauchy integral.
The estimate is uniform on each circle, using the cobounded limit itself. -/
lemma tendsto_circleIntegral_kernel_zero_of_tendsto_zero
    {f : ℂ → ℂ} (hf : Tendsto f (cobounded ℂ) (𝓝 0)) (s : ℂ) :
    Tendsto (fun R : ℝ => ∮ w in C(0, R), f w / (w - s)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / (8 * Real.pi)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) Real.pi_pos)
  have hsmall : ∀ᶠ w : ℂ in cobounded ℂ, ‖f w‖ < δ := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hf) δ hδ
  obtain ⟨M, _, hM⟩ := (Filter.hasBasis_cobounded_norm (E := ℂ)).mem_iff.mp hsmall
  filter_upwards [eventually_gt_atTop (max M (2 * ‖s‖ + 1))] with R hR
  have hRM : M ≤ R := ((le_max_left _ _).trans_lt hR).le
  have hRs : 2 * ‖s‖ + 1 < R := (le_max_right _ _).trans_lt hR
  have hRp : 0 < R := by nlinarith [norm_nonneg s]
  have hd : 0 < R - ‖s‖ := by nlinarith [norm_nonneg s]
  have hbound : ∀ w ∈ sphere (0 : ℂ) R,
      ‖f w / (w - s)‖ ≤ δ / (R - ‖s‖) := by
    intro w hw
    have hn : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right] using hw
    have hfw : ‖f w‖ ≤ δ := (hM (by simpa only [Set.mem_setOf_eq, hn] using hRM)).le
    have hden : R - ‖s‖ ≤ ‖w - s‖ := by
      simpa only [hn] using norm_sub_norm_le w s
    rw [norm_div]
    exact (div_le_div_of_nonneg_right hfw (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left hδ.le hd hden)
  have hratio : R / (R - ‖s‖) ≤ 2 := (div_le_iff₀ hd).mpr (by linarith)
  have hnorm : ‖∮ w in C(0, R), f w / (w - s)‖ ≤ ε / 2 := by
    calc
      ‖∮ w in C(0, R), f w / (w - s)‖ ≤
          2 * Real.pi * R * (δ / (R - ‖s‖)) :=
        circleIntegral.norm_integral_le_of_norm_le_const hRp.le hbound
      _ = (2 * Real.pi * δ) * (R / (R - ‖s‖)) := by ring
      _ ≤ (2 * Real.pi * δ) * 2 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = ε / 2 := by
        dsimp [δ]
        field_simp [Real.pi_ne_zero]
        <;> ring
  simpa only [dist_zero_right] using hnorm.trans_lt (by linarith : ε / 2 < ε)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem tendsto_slitPullbackNumerator_zero
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : s ≠ 0) :
    Tendsto (slitPullbackNumerator H Y a s) (cobounded ℂ) (𝓝 0) := by
  have hreg := (tendsto_regularizedReflectedTrace_zero hH hY hdet).comp
    (tendsto_slitJoukowski_cobounded ha)
  have hi : Tendsto (fun w : ℂ => w⁻¹) (cobounded ℂ) (𝓝 0) := tendsto_inv₀_cobounded
  have hi2 : Tendsto (fun w : ℂ => (w ^ 2)⁻¹) (cobounded ℂ) (𝓝 0) := by
    simpa only [inv_pow, zero_pow (by decide : 2 ≠ 0)] using hi.pow 2
  have his : Tendsto (fun w : ℂ => (w * s)⁻¹) (cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded.comp (tendsto_mul_right_cobounded hs)
  have hnum : Tendsto (fun w : ℂ => 1 - (w ^ 2)⁻¹) (cobounded ℂ) (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hi2
  have hden : Tendsto (fun w : ℂ => 1 - (w * s)⁻¹) (cobounded ℂ) (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub his
  have ht : Tendsto (fun w : ℂ =>
      regularizedReflectedTrace H Y (slitJoukowski a w) * (1 - (w ^ 2)⁻¹) /
        (1 - (w * s)⁻¹)) (cobounded ℂ) (𝓝 ((0 * 1) / 1 : ℂ)) :=
    (hreg.mul hnum).div hden (one_ne_zero : (1 : ℂ) ≠ 0)
  change Tendsto (fun w : ℂ =>
    regularizedReflectedTrace H Y (slitJoukowski a w) * (1 - (w ^ 2)⁻¹) /
      (1 - (w * s)⁻¹)) (cobounded ℂ) (𝓝 0)
  simpa only [zero_mul, zero_div] using ht

/-- The genuine outer contour of the actual derivative pullback vanishes.
The result uses the proved decay at infinity of the source remainder. -/
theorem tendsto_slitPullbackKernel_outer_zero
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 < ‖s‖) :
    Tendsto (fun R : ℝ => ∮ w in C(0, R), slitPullbackKernel H Y a s w)
      atTop (𝓝 0) := by
  have hsn : s ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hs)
  have ht := tendsto_circleIntegral_kernel_zero_of_tendsto_zero
    (tendsto_slitPullbackNumerator_zero hH hY hdet ha hsn) s
  apply Tendsto.congr' _ ht
  filter_upwards [eventually_gt_atTop ‖s‖] with R hR
  have hRp : 0 < R := (lt_trans zero_lt_one hs).trans hR
  symm
  apply circleIntegral.integral_congr hRp.le
  intro w hw
  have hn : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right] using hw
  apply slitPullbackKernel_eq_div H Y ha hs (by rw [hn]; exact hs.trans hR)
  intro hws
  exact hR.ne (hws ▸ hn)

/-- Keeping any inner ellipse outside the unit circle and enclosing no pole,
the actual integral is already independent of its radius and has this value.
Only the remaining inner limit turns this into the source density integral. -/
theorem slitPullbackKernel_inner_eq
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {a : ℝ} (ha : 0 < a)
    (hYbound : |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)| ≤ a)
    {s : ℂ} {r : ℝ} (hr : 1 < r) (hrs : r < ‖s‖) :
    (∮ w in C(0, r), slitPullbackKernel H Y a s w) =
      -(2 * Real.pi * Complex.I : ℂ) *
        regularizedReflectedTrace H Y (slitJoukowski a s) := by
  have hlim := (tendsto_slitPullbackKernel_outer_zero hH hY hdet ha (hr.trans hrs)).sub_const
    (∮ w in C(0, r), slitPullbackKernel H Y a s w)
  have hevent : (fun R : ℝ =>
      (∮ w in C(0, R), slitPullbackKernel H Y a s w) -
        (∮ w in C(0, r), slitPullbackKernel H Y a s w)) =ᶠ[atTop]
      (fun _ => (2 * Real.pi * Complex.I : ℂ) *
        regularizedReflectedTrace H Y (slitJoukowski a s)) := by
    filter_upwards [eventually_gt_atTop ‖s‖] with R hR
    exact slitPullbackKernel_annulus hH hY hdet ha hYbound hr hrs hR
  have heq := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hevent.symm)
  linear_combination -heq

end
end CGLMPBounds.Hardy
