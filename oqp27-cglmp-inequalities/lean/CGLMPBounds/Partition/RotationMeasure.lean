module

public import CGLMPBounds.Partition.CharacterRotation
public import CGLMPBounds.Partition.CountProduct

@[expose] public section


/-! Actual preservation of uniform boundary measure by fractional-part
rotation. The proof factors through the unit additive circle and derives
the [0,1) section's measure law from its almost-everywhere inverse. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

theorem boundaryUniformMeasure_rotate_preserving (origin : ℝ) :
    MeasurePreserving (fun t : ℝ => Int.fract (t - origin))
      boundaryUniformMeasure boundaryUniformMeasure := by
  let circleSection : UnitAddCircle → ℝ := fun u => (AddCircle.equivIco 1 0 u : ℝ)
  have hq : MeasurePreserving ((↑) : ℝ → UnitAddCircle)
      boundaryUniformMeasure volume := by
    unfold boundaryUniformMeasure
    rw [restrict_Ico_eq_restrict_Ioc]
    simpa using UnitAddCircle.measurePreserving_mk 0
  have hsection_meas : Measurable circleSection :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  have hsection : MeasurePreserving circleSection volume boundaryUniformMeasure := by
    refine ⟨hsection_meas, ?_⟩
    rw [← hq.map_eq, Measure.map_map hsection_meas hq.measurable]
    have hid : (circleSection ∘ ((↑) : ℝ → UnitAddCircle)) =ᵐ[boundaryUniformMeasure] id := by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ico] with t ht
      change (AddCircle.equivIco 1 0 (t : UnitAddCircle) : ℝ) = t
      rw [AddCircle.equivIco_coe_eq (show t ∈ Set.Ico (0 : ℝ) (0 + 1) by simpa using ht)]
    rw [Measure.map_congr hid]
    exact Measure.map_id
  have hcircle : MeasurePreserving (fun u : UnitAddCircle => u - (origin : UnitAddCircle))
      volume volume := measurePreserving_sub_right volume (origin : UnitAddCircle)
  have hcomp := hsection.comp (hcircle.comp hq)
  have hfun : circleSection ∘ ((fun u : UnitAddCircle => u - (origin : UnitAddCircle)) ∘
      ((↑) : ℝ → UnitAddCircle)) = (fun t : ℝ => Int.fract (t - origin)) := by
    funext t
    change (AddCircle.equivIco 1 0 ((t : UnitAddCircle) - (origin : UnitAddCircle)) : ℝ) = _
    rw [← AddCircle.coe_sub]
    simpa using AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) (t - origin)
  exact hfun ▸ hcomp

theorem rotateBoundaryPoints_measurePreserving (d : ℕ) (origin : ℝ) :
    MeasurePreserving (rotateBoundaryPoints d origin)
      (boundaryProductMeasure d) (boundaryProductMeasure d) := by
  exact measurePreserving_pi (fun _ : Fin d => boundaryUniformMeasure)
    (fun _ : Fin d => boundaryUniformMeasure)
      (fun _ => boundaryUniformMeasure_rotate_preserving origin)

theorem boundaryArcCount_rotate (d : ℕ) (origin x : ℝ) (T : Fin d → ℝ) :
    boundaryArcCount d 0 x (rotateBoundaryPoints d origin T) =
      boundaryArcCount d origin x T := by
  simp [boundaryArcCount, rotateBoundaryPoints, Int.fract_fract]

end
end CGLMPBounds.Partition
