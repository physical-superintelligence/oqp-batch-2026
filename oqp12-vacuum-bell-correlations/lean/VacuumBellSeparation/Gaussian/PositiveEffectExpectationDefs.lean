module

public import VacuumBellSeparation.Gaussian.PositiveTrace

@[expose] public section


noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def positiveEffectExpectation (ρ M : E →L[ℂ] E) : ℝ≥0∞ :=
  positiveTrace (CFC.sqrt M * ρ * CFC.sqrt M)

end VacuumBellSeparation.Gaussian
