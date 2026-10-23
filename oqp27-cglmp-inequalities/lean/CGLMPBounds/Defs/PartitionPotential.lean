module

public import CGLMPBounds.Defs.PartitionMixture

@[expose] public section


/-! The literal source potential (D.5), with its three removable values.
Its Fourier coefficient is the actual fourth-derivative integral printed
after (D.9). No positivity, summability, or Fourier identity is assumed. -/

namespace CGLMPBounds.Partition
noncomputable section

def partitionPotential (x : ℝ) : ℝ :=
  if x = 0 ∨ x = 1 then 0
  else if x = 1 / 2 then Real.sqrt 2 / Real.pi ^ 2 - 1 / 8
  else -(x * (1 - x)) / 2 + (2 * x - 1) /
    (Real.pi * (1 / Real.cos (Real.pi * x / 2) - 1 / Real.sin (Real.pi * x / 2)))

/-- Index n is the positive frequency n+1. -/
def partitionFourierCoefficient (n : ℕ) : ℝ :=
  (1 / (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2)) *
    ∫ x in (0 : ℝ)..1, iteratedDeriv 4 partitionPotential x *
      (1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x))

end
end CGLMPBounds.Partition
