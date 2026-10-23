module

public import VacuumBellSeparation.Bell.EventConstants

@[expose] public section


/-!
# Upper event constants from denominator-free effect bounds

Both actual supremum definitions are bounded directly. In the reverse
direction the extended quotient retains the zero-denominator convention.
-/

namespace VacuumBellSeparation

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projections_subset_effects (M : VonNeumannAlgebra H) : projections M ⊆ effects M := by
  intro E hE
  exact ⟨hE.1, isPositive_of_mem_projections hE,
    isPositive_of_mem_projections (one_sub_mem_projections hE)⟩

theorem eventConstPlus_le_of_effect_bound (ω : State H) (M N : VonNeumannAlgebra H)
    {r K : ℝ} (hr : 1 < r)
    (hbound : ∀ E ∈ effects M, ∀ P ∈ effects N,
      (ω (E * P)).re ^ r ≤ K * ((ω E).re * (ω P).re) ^ (r - 1)) :
    eventConstPlus ω M N r ≤ ENNReal.ofReal K := by
  apply iSup_le
  intro E
  apply iSup_le
  intro hE
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  apply iSup_le
  intro hpos
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hpos (r - 1))).mpr
    (hbound E (projections_subset_effects M hE) P (projections_subset_effects N hP))

theorem eventConstMinus_le_of_effect_bound (ω : State H) (M N : VonNeumannAlgebra H)
    {r K : ℝ} (hr : 1 < r) (hK : 0 ≤ K)
    (hbound : ∀ E ∈ effects M, ∀ P ∈ effects N,
      ((ω E).re * (ω P).re) ^ r ≤ K * (ω (E * P)).re ^ (r - 1)) :
    eventConstMinus ω M N r ≤ ENNReal.ofReal K := by
  apply iSup_le
  intro E
  apply iSup_le
  intro hE
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  apply iSup_le
  intro hpos
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal
    (hbound E (projections_subset_effects M hE) P (projections_subset_effects N hP))

end VacuumBellSeparation
