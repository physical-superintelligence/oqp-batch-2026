module

public import CGLMPBounds.Hardy.SchwarzEllipseParam

@[expose] public section


/-!
# Convergence of actual shrinking ellipses to the two source banks

Continuity on a compact parameter box proves each bank's integral convergence.
The nonreal pole stays uniformly away from sufficiently flat ellipses. The
literal reflected source kernel is identified with the continuous upper or
conjugate bank on the two open parameter halves; endpoints have zero measure.
-/

open Complex Matrix Filter Set Metric MeasureTheory
open scoped Topology Interval Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

lemma continuousAt_ellipseKernelIntegral (G : ℂ → ℂ) (hG : Continuous G)
    (a u v : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ContinuousAt (fun r : ℝ => ∫ θ in u..v, slitEllipseTangent a r θ *
      (G (slitEllipse a r θ) / (slitEllipse a r θ - z))) 1 := by
  let B : ℝ → ℝ := fun t => (a / 2) * ((1 + t) - (1 + t)⁻¹)
  have hB : ContinuousAt B 0 := by
    apply continuousAt_const.mul
    exact (continuousAt_const.add continuousAt_id).sub
      ((continuousAt_const.add continuousAt_id).inv₀ (by norm_num))
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |B t| < |z.im| := by
    apply hB.abs.eventually_lt continuousAt_const
    simpa [B] using abs_pos.mpr hz
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.eventually_nhds_iff_ball.mp hsmall
  let ε : ℝ := min (δ / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεsmall : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have hr : ∀ t ∈ Icc (-ε) ε, 1 + t ≠ 0 := by
    intro t ht
    have hp : 0 < 1 + t := by linarith [ht.1]
    exact hp.ne'
  have hden : ∀ t ∈ Icc (-ε) ε, ∀ θ : ℝ, slitEllipse a (1 + t) θ - z ≠ 0 := by
    intro t ht θ he
    have hBt : |B t| < |z.im| := hδsmall t (by
      rw [mem_ball, Real.dist_eq, sub_zero]
      exact (abs_le.mpr ht).trans_lt hεsmall)
    have him := congrArg Complex.im (sub_eq_zero.mp he)
    have hb : |z.im| ≤ |B t| := by
      rw [← him, slitEllipse_im, abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (abs_nonneg _)).trans_eq
        (mul_one _)
    exact (not_le.mpr hBt) hb
  let F : ℝ → ℂ := fun r => ∫ θ in u..v, slitEllipseTangent a r θ *
    (G (slitEllipse a r θ) / (slitEllipse a r θ - z))
  have hshift : ContinuousAt (fun t : ℝ => F (1 + t)) 0 := by
    apply continuousAt_intervalIntegral_of_continuousOn_box _ u v hε
    intro p hp
    have he := (continuousAt_slitEllipse a (hr p.1 hp.1)).comp
      ((continuousAt_const.add continuousAt_fst).prodMk continuousAt_snd)
    have hd := (continuousAt_slitEllipseTangent a (hr p.1 hp.1)).comp
      ((continuousAt_const.add continuousAt_fst).prodMk continuousAt_snd)
    exact (hd.mul ((hG.continuousAt.comp he).div
      (he.sub continuousAt_const) (hden p.1 hp.1 p.2))).continuousWithinAt
  have ht : Tendsto (fun r : ℝ => r - 1) (𝓝 1) (𝓝 0) := by
    simpa only [id_eq, sub_self] using
      ((tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 (1 : ℝ)) (𝓝 1)).sub_const (1 : ℝ))
  have hh := hshift.tendsto.comp ht
  have hfun : (fun r : ℝ => F (1 + (r - 1))) = F := by
    funext r
    congr 1
    ring
  change Tendsto (fun r : ℝ => F (1 + (r - 1))) (𝓝 1) (𝓝 (F (1 + 0))) at hh
  change Tendsto F (𝓝 1) (𝓝 (F 1))
  simpa only [hfun, add_zero] using hh

lemma slitEllipse_im_pos {a r θ : ℝ} (ha : 0 < a) (hr : 1 < r)
    (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) : 0 < (slitEllipse a r θ).im := by
  have hi : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr.le
  rw [slitEllipse_im]
  exact mul_pos (mul_pos (div_pos ha (by norm_num)) (by linarith))
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

lemma slitEllipse_im_neg {a r θ : ℝ} (ha : 0 < a) (hr : 1 < r)
    (hθ : θ ∈ Ioo Real.pi (2 * Real.pi)) : (slitEllipse a r θ).im < 0 := by
  have hi : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr.le
  have hs : Real.sin θ < 0 := by
    have hp := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1] : 0 < θ - Real.pi)
      (by linarith [hθ.2] : θ - Real.pi < Real.pi)
    rw [Real.sin_sub_pi] at hp
    linarith
  rw [slitEllipse_im]
  exact mul_neg_of_pos_of_neg
    (mul_pos (div_pos ha (by norm_num)) (by linarith)) hs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- The synthetic bank integral uses globally continuous actual boundary
extensions; it is then identified with the literal ellipse contour below. -/
def regularizedEllipseBanks (H Y : Matrix ι ι ℂ) (a r : ℝ) (z : ℂ) : ℂ :=
  (∫ θ in (0 : ℝ)..Real.pi, slitEllipseTangent a r θ *
    (regularizedFoldedUpperTrace H Y (slitEllipse a r θ) / (slitEllipse a r θ - z))) +
  (∫ θ in Real.pi..(2 * Real.pi), slitEllipseTangent a r θ *
    (star (regularizedFoldedUpperTrace H Y (slitEllipse a r θ)) /
      (slitEllipse a r θ - z)))

theorem tendsto_regularizedEllipseBanks
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun r : ℝ => regularizedEllipseBanks H Y a r z) (𝓝[>] (1 : ℝ))
      (𝓝 (-(2 * Real.pi * Complex.I : ℂ) *
        ∫ x in (-a)..a, (traceDensity H Y x : ℂ) / ((x : ℂ) - z))) := by
  have hG := continuous_regularizedFoldedUpperTrace hH hY hdet
  have hu := continuousAt_ellipseKernelIntegral _ hG a 0 Real.pi hz
  have hl := continuousAt_ellipseKernelIntegral _ hG.star a Real.pi (2 * Real.pi) hz
  have ht := (hu.tendsto.add hl.tendsto).mono_left
    (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
  change Tendsto (fun r : ℝ => regularizedEllipseBanks H Y a r z) (𝓝[>] (1 : ℝ))
    (𝓝 (regularizedEllipseBanks H Y a 1 z)) at ht
  have he : regularizedEllipseBanks H Y a 1 z =
      -(2 * Real.pi * Complex.I : ℂ) *
        ∫ x in (-a)..a, (traceDensity H Y x : ℂ) / ((x : ℂ) - z) := by
    simpa only [regularizedEllipseBanks, slitEllipse_one, slitEllipseTangent_one,
      Complex.real_smul] using integral_regularized_cosineBanks hH hY hdet a hz
  rwa [he] at ht

theorem circleIntegral_slitPullbackKernel_eq_banks
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {a : ℝ} (ha : 0 < a)
    (hYbound : |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)| ≤ a)
    {s : ℂ} {r : ℝ} (hr : 1 < r) (hrs : r < ‖s‖) :
    (∮ w in C(0, r), slitPullbackKernel H Y a s w) =
      regularizedEllipseBanks H Y a r (slitJoukowski a s) := by
  have hrp : 0 < r := lt_trans zero_lt_one hr
  have hrn : r ≠ 0 := hrp.ne'
  have hs : 1 < ‖s‖ := hr.trans hrs
  have hw : ∀ θ : ℝ, 1 < ‖circleMap 0 r θ‖ := by
    intro θ
    simpa only [norm_circleMap_zero, abs_of_pos hrp] using hr
  have hden : ∀ θ : ℝ, slitEllipse a r θ - slitJoukowski a s ≠ 0 := by
    intro θ he
    have heq : slitJoukowski a (circleMap 0 r θ) = slitJoukowski a s := by
      rw [slitJoukowski_circleMap]
      exact sub_eq_zero.mp he
    have hws := slitJoukowski_injOn ha (hw θ) hs heq
    have hn := congrArg norm hws
    simp only [norm_circleMap_zero, abs_of_pos hrp] at hn
    exact hrs.ne hn
  have hE : Continuous (slitEllipse a r) := continuous_iff_continuousAt.mpr
    (fun θ => (hasDerivAt_slitEllipse a r θ).continuousAt)
  have hD : Continuous (slitEllipseTangent a r) := continuous_iff_continuousAt.mpr
    (fun θ => (continuousAt_slitEllipseTangent a hrn).comp
      (continuousAt_const.prodMk continuousAt_id))
  have hG : Continuous (fun θ => regularizedReflectedTrace H Y (slitEllipse a r θ)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hslit : slitEllipse a r θ ∉ spectralSlit Y := by
      rw [← slitJoukowski_circleMap]
      exact slitJoukowski_not_mem_spectralSlit Y ha hYbound (hw θ)
    exact (analyticOnNhd_regularizedReflectedTrace hH hY hdet _ hslit).continuousAt.comp
      hE.continuousAt
  have hF : Continuous (fun θ => slitEllipseTangent a r θ *
      (regularizedReflectedTrace H Y (slitEllipse a r θ) /
        (slitEllipse a r θ - slitJoukowski a s))) :=
    hD.mul (hG.div (hE.sub continuous_const) hden)
  rw [circleIntegral_slitPullbackKernel_eq_ellipse H Y a s hrn,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable 0 Real.pi) (hF.intervalIntegrable Real.pi (2 * Real.pi))]
  unfold regularizedEllipseBanks
  congr 1
  · apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
    intro θ hθ
    dsimp only
    rw [regularizedFoldedUpperTrace_eq_of_nonneg H Y (slitEllipse_im_pos ha hr hθ).le]
  · apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [Real.pi_pos])
    intro θ hθ
    dsimp only
    rw [regularizedFoldedUpperTrace_star_eq_of_neg hH hY hdet (slitEllipse_im_neg ha hr hθ)]

/-- Actual shrinking-ellipse limit, including its orientation and exact source
density. All analytic/boundary data refer to the literal Hermitian pencil. -/
theorem tendsto_slitPullbackKernel_inner
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {a : ℝ} (ha : 0 < a)
    (hYbound : |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)| ≤ a)
    {s : ℂ} (hs : 1 < ‖s‖) (hz : (slitJoukowski a s).im ≠ 0) :
    Tendsto (fun r : ℝ => ∮ w in C(0, r), slitPullbackKernel H Y a s w)
      (𝓝[>] (1 : ℝ))
      (𝓝 (-(2 * Real.pi * Complex.I : ℂ) *
        ∫ x in (-a)..a, (traceDensity H Y x : ℂ) / ((x : ℂ) - slitJoukowski a s))) := by
  apply Tendsto.congr' _ (tendsto_regularizedEllipseBanks hH hY hdet a hz)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hs).filter_mono nhdsWithin_le_nhds] with r hr hrs
  exact (circleIntegral_slitPullbackKernel_eq_banks hH hY hdet ha hYbound hr hrs).symm

end
end CGLMPBounds.Hardy
