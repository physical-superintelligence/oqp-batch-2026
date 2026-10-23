module

public import VacuumBellSeparation.Fock.WeylFockEquivalence
public import VacuumBellSeparation.FreeField.Existence

@[expose] public section


/-!
# Literal symmetric Fock carrier and original vacuum vector

This construction is separated from its later specification proofs.
-/

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory Fock
open scoped InnerProductSpace

variable {m : ℝ} (hm : 0 < m)

abbrev LiteralFockSpace := SymmetricFockSpace (Lp ℂ 2 (oneParticleMeasure m))

def literalFockVacuumVector : LiteralFockSpace (m := m) :=
  coherentVector (Lp ℂ 2 (oneParticleMeasure m)) 0


end VacuumBellSeparation
