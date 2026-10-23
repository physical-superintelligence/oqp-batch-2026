module

public import VacuumBellSeparation.Gaussian.PhysicalGaussianTransport
public import VacuumBellSeparation.Gaussian.UnitarySandwich
public import VacuumBellSeparation.Gaussian.GaussianAppendixA

@[expose] public section


/-!
# Literal statement construction extracted from Gaussian/GaussianWilliamsonSandwich

The moved declarations retain their original text. Later target proofs remain separate.
-/

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ}

def williamsonSandwichCovariance (q : Fin m → ℝ) (τ : ℝ)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  let T := modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ));
  -T + CFC.sqrt (T ^ 2 - (1 / 4 : ℝ) • 1) * (T - V)⁻¹ *
    CFC.sqrt (T ^ 2 - (1 / 4 : ℝ) • 1)


end VacuumBellSeparation.Gaussian
