module

public import CGLMPBounds.Defs.ScalarBeta

@[expose] public section


/-!
# Actual uniform boundary points and one Fourier-power tilt

The probability space is the product of literal Lebesgue restrictions to
`[0,1)`. The d coordinates are labelled boundary points on the unit circle.
The count uses fractional parts, hence represents the arc from an arbitrary
real origin modulo one. Density normalization, rotation invariance, and the
count laws are theorem obligations, not fields or assumptions of this file.
These definitions cover the single-mode ingredient of (D.10)–(D.11); the
general v-series mixture and circular partition/Hardy-form map are separate.
-/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

def boundaryUniformMeasure : Measure ℝ :=
  volume.restrict (Set.Ico (0 : ℝ) 1)

def boundaryProductMeasure (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ : Fin d => boundaryUniformMeasure)

def boundaryCharacter (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ) * Complex.I)

/-- The source's single Fourier-power density, normalized by 1/d. -/
def fourierBoundaryDensity (d n : ℕ) (T : Fin d → ℝ) : ℝ :=
  ‖∑ j : Fin d, boundaryCharacter n (T j)‖ ^ 2 / (d : ℝ)

def fourierBoundaryMeasure (d n : ℕ) : Measure (Fin d → ℝ) :=
  (boundaryProductMeasure d).withDensity
    (fun T => ENNReal.ofReal (fourierBoundaryDensity d n T))

def rotateBoundaryPoints (d : ℕ) (origin : ℝ) (T : Fin d → ℝ) : Fin d → ℝ :=
  fun j => Int.fract (T j - origin)

def boundaryArcCount (d : ℕ) (origin x : ℝ) (T : Fin d → ℝ) : ℕ :=
  (Finset.univ.filter (fun j : Fin d => Int.fract (T j - origin) < x)).card

def fourierTiltShape (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin (Real.pi * (n : ℝ) * x) ^ 2 / (Real.pi ^ 2 * (n : ℝ) ^ 2)

end
end CGLMPBounds.Partition
