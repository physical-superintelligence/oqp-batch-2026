module

public import VacuumBellSeparation.FreeField.JointPolynomialMomentRange
public import VacuumBellSeparation.FreeField.JointPolynomialErrorOperators

@[expose] public section


/-! # A genuine moment family for the actual union of source balls -/

noncomputable section
namespace VacuumBellSeparation

open Set Metric

def jointSourceMomentRadius (s : ℝ) : ℝ := 2 + ‖spatialAxisDisplacement s 0‖

theorem jointSourceMomentRadius_pos (s : ℝ) : 0 < jointSourceMomentRadius s := by
  unfold jointSourceMomentRadius
  positivity

theorem jointSourceRegion_subset_moment_ball (s : ℝ) :
    jointSourceRegion s ⊆ ball 0 (jointSourceMomentRadius s) := by
  intro x hx
  simp only [jointSourceRegion, jointCenterIndex_zero, jointCenterIndex_one,
    mem_union, mem_ball, dist_zero_right] at hx
  rw [mem_ball, dist_zero_right]
  rcases hx with hx | hx
  · exact hx.trans (by unfold jointSourceMomentRadius; linarith [norm_nonneg (spatialAxisDisplacement s 0)])
  · have hn := norm_add_le (x - spatialAxisDisplacement s 0) (spatialAxisDisplacement s 0)
    rw [sub_add_cancel] at hn
    rw [dist_eq_norm] at hx
    unfold jointSourceMomentRadius
    linarith

/-- Chosen only after the actual moment-vector theorem and region geometry
have discharged existence. The family has no additional assumption. -/
def jointRegionMomentFamily {μ : ℝ} (hμ : 0 < μ) (s : ℝ) :
    JointSourceMomentFamily hμ (jointSourceRegion s) :=
  jointSourceMomentFamily hμ (jointSourceMomentRadius_pos s) (jointSourceRegion s)
    (jointSourceRegion_subset_moment_ball s)

end VacuumBellSeparation
