module

public import CGLMPBounds.Defs.PartitionProbability

@[expose] public section


/-! Actual positive-frequency mixtures of the boundary densities in (D.10).
The sequence index n denotes frequency n+1. These definitions assume no
positivity, convergence, normalization, count law, or identification with the
specific v in (D.5). Such properties are separate theorem obligations. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

def fourierMixtureResidual (a : ℕ → ℝ) : ℝ := 1 - ∑' n, a n

def fourierMixtureDensity (d : ℕ) (a : ℕ → ℝ) (T : Fin d → ℝ) : ℝ :=
  fourierMixtureResidual a + ∑' n, a n * fourierBoundaryDensity d (n + 1) T

def fourierMixtureMeasure (d : ℕ) (a : ℕ → ℝ) : Measure (Fin d → ℝ) :=
  (boundaryProductMeasure d).withDensity
    (fun T => ENNReal.ofReal (fourierMixtureDensity d a T))

def fourierMixtureShape (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, a n * fourierTiltShape (n + 1) x

end
end CGLMPBounds.Partition
