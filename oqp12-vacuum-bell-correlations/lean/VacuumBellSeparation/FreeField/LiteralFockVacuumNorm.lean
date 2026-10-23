module

public import VacuumBellSeparation.FreeField.LiteralFockVacuumDefs

@[expose] public section


/-!
# Norm of the actual literal Fock vacuum vector

This construction is separated from its later specification proofs.
-/

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory Fock
open scoped InnerProductSpace

variable {m : ℝ} (hm : 0 < m)

theorem literalFockVacuumVector_norm : ‖literalFockVacuumVector (m := m)‖ = 1 := by
  rw [literalFockVacuumVector, ← weylFockEquiv_weylVec, LinearIsometryEquiv.norm_map]
  exact norm_weylVec_zero _ (fun _ _ => rfl)


end VacuumBellSeparation
