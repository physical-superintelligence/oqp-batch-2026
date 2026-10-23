module

public import Mathlib

@[expose] public section


/-!
# Statement seed extracted from FreeField/CanonicalContractionExhaustion

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

namespace VacuumBellSeparation

open Filter Topology
open scoped InnerProductSpace

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def vacuumComplexCovariance (Ω : H) (A B : H →L[ℂ] H) : ℂ :=
  ⟪Ω, (A * B) Ω⟫_ℂ - ⟪Ω, A Ω⟫_ℂ * ⟪Ω, B Ω⟫_ℂ


end VacuumBellSeparation
