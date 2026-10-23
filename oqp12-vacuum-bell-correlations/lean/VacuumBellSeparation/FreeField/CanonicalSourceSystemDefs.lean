module

public import VacuumBellSeparation.FreeField.TimeZeroSymplecticNondegenerate
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section


/-!
# Literal statement construction extracted from FreeField/CanonicalSourceHull

The moved declarations retain their original text. Later target proofs remain separate.
-/

namespace VacuumBellSeparation

/-- A canonical system retains the actual local test pairs and symplectic form. -/
def IsCanonicalSourceSystem (U : Set (EuclideanSpace ℝ (Fin 3)))
    (S : Submodule ℝ TimeZeroSource) : Prop :=
  FiniteDimensional ℝ S ∧ S ≤ localizedTimeZeroSources U ∧
    ∀ u ∈ S, (∀ v ∈ S, timeZeroSymplectic u v = 0) → u = 0


end VacuumBellSeparation
