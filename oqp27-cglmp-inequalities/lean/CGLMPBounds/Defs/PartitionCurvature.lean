module

public import CGLMPBounds.Defs.PartitionMixture

@[expose] public section


/-! Literal Fourier derivative series for the structural partition mixture.
The derivative equalities are proved separately; they are not definitions. -/

namespace CGLMPBounds.Partition
noncomputable section

def fourierTiltSlope (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin (2 * Real.pi * (n : ℝ) * x) / (Real.pi * (n : ℝ))

def fourierMixtureSlope (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, a n * fourierTiltSlope (n + 1) x

def fourierMixtureCurvature (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, a n * (2 * Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x))

end
end CGLMPBounds.Partition
