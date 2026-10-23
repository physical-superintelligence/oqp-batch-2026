module

public import VacuumBellSeparation.Gaussian.IntrinsicGaussianPerturbationDefs
public import VacuumBellSeparation.Gaussian.GaussianRenyiParameters

@[expose] public section


/-!
# Literal Gaussian Renyi exponential coefficient

This construction is separated from its later specification proofs.
-/

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal Matrix.Norms.L2Operator

variable {m : ℕ}
  {ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
  {Vρ Vσ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

noncomputable def gaussianRenyiExponent (ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (r : ℝ) : ℝ :=
  2 * r * max 2 (gaussianRenyiTau r)⁻¹ *
    matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ (gaussianRenyiTau r))


end VacuumBellSeparation.Gaussian
