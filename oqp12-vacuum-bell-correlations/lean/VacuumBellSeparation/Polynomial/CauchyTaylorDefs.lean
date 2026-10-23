module

public import VacuumBellSeparation.Gaussian.PolydiscCoefficientDefs
public import Mathlib.Data.Fintype.Pi

@[expose] public section


namespace VacuumBellSeparation

open scoped BigOperators
open Gaussian

/-- All multiindices of total degree strictly less than N, including the
empty index precisely when N is positive. -/
def multiIndexBelow (d N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.range N)).filter (fun k => ∑ j, k j < N)

/-- The actual Taylor polynomial, evaluated at x. -/
noncomputable def cauchyTaylor (d N : ℕ) (R : ℝ)
    (F : (Fin d → ℂ) → ℂ) (x : Fin d → ℂ) : ℂ :=
  ∑ k ∈ multiIndexBelow d N, polydiscCoefficient d R F k * ∏ j, x j ^ k j

end VacuumBellSeparation
