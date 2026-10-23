module

public import CGLMPBounds.Defs.PartitionProbability

@[expose] public section


/-! Elementary actual-measure foundations for the single Fourier-power tilt.
No normalization or count-law identity is assumed here. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

instance boundaryUniformMeasure_isProbabilityMeasure :
    IsProbabilityMeasure boundaryUniformMeasure where
  measure_univ := by simp [boundaryUniformMeasure, Real.volume_Ico]

instance boundaryProductMeasure_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (boundaryProductMeasure d) := by
  unfold boundaryProductMeasure
  infer_instance

theorem boundary_coordinates_independent (d : ℕ) :
    ProbabilityTheory.iIndepFun (fun j : Fin d => fun T : Fin d → ℝ => T j)
      (boundaryProductMeasure d) := by
  simpa only [boundaryProductMeasure, id_eq] using
    (ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin d => boundaryUniformMeasure)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id))

theorem boundaryCharacter_norm (n : ℕ) (t : ℝ) : ‖boundaryCharacter n t‖ = 1 := by
  simp [boundaryCharacter, Complex.norm_exp]

theorem fourierBoundaryDensity_nonneg (d n : ℕ) (T : Fin d → ℝ) :
    0 ≤ fourierBoundaryDensity d n T := by
  exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

theorem fourierBoundaryDensity_le (d n : ℕ) (T : Fin d → ℝ) :
    fourierBoundaryDensity d n T ≤ d := by
  by_cases hd : d = 0
  · subst d
    simp [fourierBoundaryDensity]
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hsum : ‖∑ j : Fin d, boundaryCharacter n (T j)‖ ≤ (d : ℝ) := by
    calc
      _ ≤ ∑ j : Fin d, ‖boundaryCharacter n (T j)‖ := norm_sum_le _ _
      _ = (d : ℝ) := by simp [boundaryCharacter_norm]
  have hprod := mul_nonneg (sub_nonneg.mpr hsum)
    (add_nonneg hdpos.le (norm_nonneg (∑ j : Fin d, boundaryCharacter n (T j))))
  unfold fourierBoundaryDensity
  apply (div_le_iff₀ hdpos).mpr
  nlinarith

theorem continuous_fourierBoundaryDensity (d n : ℕ) :
    Continuous (fourierBoundaryDensity d n) := by
  unfold fourierBoundaryDensity boundaryCharacter
  fun_prop

theorem integrable_fourierBoundaryDensity (d n : ℕ) :
    Integrable (fourierBoundaryDensity d n) (boundaryProductMeasure d) := by
  apply (integrable_const (d : ℝ)).mono'
    (continuous_fourierBoundaryDensity d n).aestronglyMeasurable
  filter_upwards [] with T
  rw [Real.norm_of_nonneg (fourierBoundaryDensity_nonneg d n T)]
  exact fourierBoundaryDensity_le d n T

theorem boundaryArcCount_le (d : ℕ) (origin x : ℝ) (T : Fin d → ℝ) :
    boundaryArcCount d origin x T ≤ d := by
  unfold boundaryArcCount
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

end
end CGLMPBounds.Partition
