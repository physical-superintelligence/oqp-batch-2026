module

public import CGLMPBounds.Defs.TraceDensity

@[expose] public section


/-! Literal objects of source C.4, equations C.10–C.12. The measure is the
actual Lebesgue density on the open x strip; finiteness, support, mass and
polynomial trace identities are theorem obligations, not structure fields. -/

namespace CGLMPBounds
open MeasureTheory
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positivePinchingPart (B Y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • (Y + B * Y * B)

def positivePinchingOffdiag (B Y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Y - positivePinchingPart B Y

/-- The exact omega in C.11, with all characteristic-root multiplicities. -/
def positivePinchingOmega (B Y : Matrix ι ι ℂ) (x y : ℝ) : ℝ :=
  (((B - (x : ℂ) • (1 : Matrix ι ι ℂ)) *
      (Y - (y : ℂ) • (1 : Matrix ι ι ℂ))).charpoly.roots.map
        (fun z : ℂ => |z.im|)).sum / (2 * Real.pi * Fintype.card ι)

/-- C.11's actual density, set to zero at and outside the x strip. -/
def positivePinchingDensity (B Y : Matrix ι ι ℂ) (p : ℝ × ℝ) : ℝ :=
  if p.1 ∈ Set.Ioo (-1 : ℝ) 1 then
    positivePinchingOmega B Y p.1 p.2 / (1 - p.1 ^ 2)
  else 0

def positivePinchingMeasure (B Y : Matrix ι ι ℂ) : Measure (ℝ × ℝ) :=
  volume.withDensity (fun p => ENNReal.ofReal (positivePinchingDensity B Y p))

/-- Literal evaluation of a scalar polynomial at a matrix, then normalized trace. -/
def normalizedPolynomialTrace (f : Polynomial ℂ) (A : Matrix ι ι ℂ) : ℂ :=
  Matrix.trace (∑ k ∈ f.support, (f.coeff k) • A ^ k) / (Fintype.card ι : ℂ)

end
end CGLMPBounds
