module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros

@[expose] public section


/-!
# A genuine one-pole Cauchy identity on a circular annulus

The removable part is Mathlib's derivative-filled `dslope`, whose analyticity
at the removed point follows from the actual power series of the numerator.
Annular Cauchy--Goursat and the disk Cauchy formula then account for the pole.
This is an auxiliary calculus lemma for C.8, with no residue or deformation
oracle in its hypotheses.
-/

open Complex Filter Set Metric
open scoped Topology

namespace CGLMPBounds.Hardy
noncomputable section

lemma differentiableAt_dslope_of_analyticAt {f : ℂ → ℂ} {s w : ℂ}
    (hs : AnalyticAt ℂ f s) (hw : DifferentiableAt ℂ f w) :
    DifferentiableAt ℂ (dslope f s) w := by
  by_cases hws : w = s
  · subst w
    obtain ⟨p, hp⟩ := hs
    exact hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt
  · exact (differentiableAt_dslope_of_ne hws).mpr hw

lemma circleIntegral_kernel_eq_dslope_add {f : ℂ → ℂ} {s : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hc : ContinuousOn (dslope f s) (sphere 0 R))
    (hne : ∀ w ∈ sphere (0 : ℂ) R, w ≠ s) :
    (∮ w in C(0, R), f w / (w - s)) =
      (∮ w in C(0, R), dslope f s w) +
        f s * (∮ w in C(0, R), (w - s)⁻¹) := by
  have hi : ContinuousOn (fun w : ℂ => (w - s)⁻¹) (sphere 0 R) :=
    (continuousOn_id.sub continuousOn_const).inv₀
      (fun w hw => sub_ne_zero.mpr (hne w hw))
  have hm : CircleIntegrable (fun w : ℂ => f s * (w - s)⁻¹) 0 R :=
    ((continuousOn_const (c := f s)).mul hi).circleIntegrable hR
  calc
    (∮ w in C(0, R), f w / (w - s)) =
        ∮ w in C(0, R), dslope f s w + f s * (w - s)⁻¹ := by
      apply circleIntegral.integral_congr hR
      intro w hw
      have hd : (w - s) * dslope f s w = f w - f s := by
        simpa only [smul_eq_mul] using sub_smul_dslope f s w
      have hn : w - s ≠ 0 := sub_ne_zero.mpr (hne w hw)
      apply (div_eq_iff hn).mpr
      calc
        f w = (w - s) * dslope f s w + f s := by linear_combination -hd
        _ = (dslope f s w + f s * (w - s)⁻¹) * (w - s) := by
          field_simp [hn]
          <;> ring
    _ = (∮ w in C(0, R), dslope f s w) +
        f s * (∮ w in C(0, R), (w - s)⁻¹) := by
      rw [circleIntegral.integral_add (hc.circleIntegrable hR) hm,
        circleIntegral.integral_const_mul]

lemma circleIntegral_sub_inv_eq_zero_of_radius_lt {s : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hrs : r < ‖s‖) :
    (∮ w in C(0, r), (w - s)⁻¹) = 0 := by
  have hne : ∀ w ∈ closedBall (0 : ℂ) r, w - s ≠ 0 := by
    intro w hw hws
    have he : w = s := sub_eq_zero.mp hws
    have hn : ‖w‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hw
    exact (not_le.mpr hrs) (he ▸ hn)
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hr (s := ∅) Set.countable_empty
  · exact (continuousOn_id.sub continuousOn_const).inv₀ hne
  · intro w hw
    exact (differentiableAt_id.sub_const s).inv
      (hne w (ball_subset_closedBall hw.1))

/-- The pole is strictly between the circles. Both circles have positive
orientation, so the outer integral minus the inner integral is the residue
contribution. The numerator is genuinely analytic near the closed annulus. -/
theorem circleIntegral_kernel_sub_eq_of_analyticOnNhd_annulus
    {f : ℂ → ℂ} {s : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrs : r < ‖s‖) (hsR : ‖s‖ < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R \ ball 0 r)) :
    (∮ w in C(0, R), f w / (w - s)) -
      (∮ w in C(0, r), f w / (w - s)) =
        (2 * Real.pi * Complex.I : ℂ) * f s := by
  have hrR : r < R := hrs.trans hsR
  have hs : s ∈ closedBall (0 : ℂ) R \ ball 0 r := by
    simp only [mem_diff, mem_closedBall, mem_ball, dist_zero_right]
    exact ⟨hsR.le, not_lt.mpr hrs.le⟩
  have hd : ∀ w ∈ closedBall (0 : ℂ) R \ ball 0 r,
      DifferentiableAt ℂ (dslope f s) w := by
    intro w hw
    exact differentiableAt_dslope_of_analyticAt (hf s hs) (hf w hw).differentiableAt
  have hc : ContinuousOn (dslope f s) (closedBall 0 R \ ball 0 r) :=
    fun w hw => (hd w hw).continuousAt.continuousWithinAt
  have heq : (∮ w in C(0, R), dslope f s w) =
      ∮ w in C(0, r), dslope f s w := by
    apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      hr hrR.le (s := ∅) Set.countable_empty hc
    intro w hw
    apply hd w
    rcases hw.1 with ⟨hwR, hwr⟩
    exact ⟨ball_subset_closedBall hwR, fun h => hwr (ball_subset_closedBall h)⟩
  have houter : sphere (0 : ℂ) R ⊆ closedBall 0 R \ ball 0 r := by
    intro w hw
    have hn : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right] using hw
    simp only [mem_diff, mem_closedBall, mem_ball, dist_zero_right, hn]
    exact ⟨le_rfl, not_lt.mpr hrR.le⟩
  have hinner : sphere (0 : ℂ) r ⊆ closedBall 0 R \ ball 0 r := by
    intro w hw
    have hn : ‖w‖ = r := by simpa only [mem_sphere, dist_zero_right] using hw
    simp only [mem_diff, mem_closedBall, mem_ball, dist_zero_right, hn]
    exact ⟨hrR.le, lt_irrefl _⟩
  have hneR : ∀ w ∈ sphere (0 : ℂ) R, w ≠ s := by
    intro w hw hws
    have hn : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right] using hw
    exact hsR.ne (hws ▸ hn)
  have hner : ∀ w ∈ sphere (0 : ℂ) r, w ≠ s := by
    intro w hw hws
    have hn : ‖w‖ = r := by simpa only [mem_sphere, dist_zero_right] using hw
    exact hrs.ne ((hws ▸ hn).symm)
  rw [circleIntegral_kernel_eq_dslope_add (hr.trans hrR).le (hc.mono houter) hneR,
    circleIntegral_kernel_eq_dslope_add hr.le (hc.mono hinner) hner,
    circleIntegral_sub_inv_eq_zero_of_radius_lt hr.le hrs,
    circleIntegral.integral_sub_inv_of_mem_ball
      (by simpa only [mem_ball, dist_zero_right] using hsR), heq]
  ring

end
end CGLMPBounds.Hardy
