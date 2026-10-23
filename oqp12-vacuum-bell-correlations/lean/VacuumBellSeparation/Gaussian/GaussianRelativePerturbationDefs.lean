module

public import VacuumBellSeparation.Gaussian.GaussianSandwichTraceRatio

@[expose] public section


/-!
# Literal statement construction extracted from Gaussian/GaussianAppendixA

The moved declarations retain their original text. Later target proofs remain separate.
-/

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
variable {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

def gaussianRelativePerturbation (q : Fin m → ℝ) (τ : ℝ)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  normalizedPerturbation (CFC.sqrt (thermalReferenceGap q τ))
    (V - thermalReferenceCovariance q)


end VacuumBellSeparation.Gaussian
