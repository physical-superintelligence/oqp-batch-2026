module

public import VacuumBellSeparation.Gaussian.GaussianCovarianceUniqueness
public import VacuumBellSeparation.Gaussian.RelativeCovarianceCongruence

@[expose] public section


/-!
# Actual normalized-power covariance increment and intrinsic perturbation

This construction is separated from its later specification proofs.
-/

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped Matrix.Norms.L2Operator

variable {m : ℕ}
variable {ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
variable {Vρ Vσ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

def gaussianPowerIncrement
    (σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) (τ : ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  normalizedGaussianPowerCovariance σ τ - gaussianPhysicalCovariance σ

def intrinsicGaussianRelativePerturbation
    (ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) (τ : ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  relativeCovariancePerturbation (gaussianPowerIncrement σ τ)
    (gaussianPhysicalCovariance ρ - gaussianPhysicalCovariance σ)


end VacuumBellSeparation.Gaussian
