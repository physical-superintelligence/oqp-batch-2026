module

public import VacuumBellSeparation.Gaussian.WilliamsonFinite

@[expose] public section


/-!
# Literal complexification and physical quantum covariance

This construction is separated from its later specification proofs.
-/

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq η]

def complexifyMatrix (M : Matrix ι κ ℝ) : Matrix ι κ ℂ :=
  M.map (algebraMap ℝ ℂ)


def quantumCovariance (V Ω : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  complexifyMatrix V + (Complex.I / 2) • complexifyMatrix Ω


end VacuumBellSeparation.Gaussian
