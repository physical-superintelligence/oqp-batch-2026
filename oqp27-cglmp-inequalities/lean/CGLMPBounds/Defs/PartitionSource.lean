module

public import CGLMPBounds.Defs.PartitionPotential

@[expose] public section


/-! The literal source probability measure from D.9–D.11, using the actual
integral coefficients defined from the D.5 potential. Positivity, mass,
normalization and count law are theorem obligations, not structure fields. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

def sourcePartitionDensity (d : ℕ) : (Fin d → ℝ) → ℝ :=
  fourierMixtureDensity d partitionFourierCoefficient

def sourcePartitionMeasure (d : ℕ) : Measure (Fin d → ℝ) :=
  fourierMixtureMeasure d partitionFourierCoefficient

/-- Periodic second derivative of the literal potential, retaining the
compact one-sided value at the joined endpoints. -/
def sourcePeriodicCurvature (x : ℝ) : ℝ :=
  iteratedDerivWithin 2 partitionPotential (Set.Icc (0 : ℝ) 1) (Int.fract x)

end
end CGLMPBounds.Partition
