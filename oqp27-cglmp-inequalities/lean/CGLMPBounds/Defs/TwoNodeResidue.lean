module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

@[expose] public section


/-!
# The literal contour residue in supplement C.9

This is a definition only. It integrates the source rational function around
`a` on the circle of radius `|a-b|/2`, with normalization `1/(2*pi*I)`.
No derivative identity or closed-form residue is part of the definition.
-/

open Complex Metric Set
open scoped Real

namespace CGLMPBounds.Hardy
noncomputable section

/-- A genuine contour definition, independent of the eventual closed form. -/
def twoNodeResidue (p q : ℕ) (a b : ℝ) : ℂ :=
  (∮ z in C((a : ℂ), |a - b| / 2),
    z ^ (p + q - 2) / ((z - (a : ℂ)) ^ p * (z - (b : ℂ)) ^ q)) /
      (2 * Real.pi * Complex.I : ℂ)

end
end CGLMPBounds.Hardy
