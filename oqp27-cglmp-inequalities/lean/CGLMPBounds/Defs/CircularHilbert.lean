module

public import CGLMPBounds.Defs.PartitionHardy
public import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section


/-! Literal circle functions and circular Hilbert transform from C.16.
The circle measure has total mass one. The scalar Hilbert transform is an
actual series in L², whose convergence and multiplier identities are theorem
obligations. The chosen L² representative is used only up to almost-everywhere
equality. No Parseval identity, involution property or Hardy bound is assumed. -/

namespace CGLMPBounds.Hardy
open MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev UnitCircle := AddCircle (1 : ℝ)
abbrev circleMeasure : Measure UnitCircle := AddCircle.haarAddCircle
abbrev CircleL2 := Lp ℂ 2 circleMeasure

/-- The multiplier is zero at frequency zero. -/
def hilbertMultiplier (k : ℤ) : ℂ := -Complex.I * (k.sign : ℂ)

/-- The actual L² Fourier series, not a pointwise series. -/
def scalarHilbertLp (f : UnitCircle → ℂ) : CircleL2 :=
  ∑' k : ℤ, (hilbertMultiplier k * fourierCoeff f k) • fourierLp (T := 1) 2 k

/-- A chosen measurable representative of the L² Hilbert transform. -/
def scalarHilbert (f : UnitCircle → ℂ) (t : UnitCircle) : ℂ :=
  scalarHilbertLp f t

def matrixHilbert {r : ℕ} (F : UnitCircle → Circulation.Mat r)
    (t : UnitCircle) : Circulation.Mat r :=
  fun i j => scalarHilbert (fun s => F s i j) t

def matrixCircleFourierCoefficient {r : ℕ}
    (F : UnitCircle → Circulation.Mat r) (k : ℤ) : Circulation.Mat r :=
  fourierCoeff F k

def matrixCircleNegativeEnergy {r : ℕ}
    (F : UnitCircle → Circulation.Mat r) : ℝ :=
  ∑' n : ℕ, Circulation.hsSq (matrixCircleFourierCoefficient F (-((n+1 : ℕ) : ℤ)))

def matrixCircleEnergy {r : ℕ} (F : UnitCircle → Circulation.Mat r) : ℝ :=
  ∫ t, Circulation.hsSq (F t) ∂circleMeasure

/-- The interval model is identified with the circle through (0,1]. -/
def intervalCircleLift {r : ℕ} (U : ℝ → Circulation.Mat r) :
    UnitCircle → Circulation.Mat r := AddCircle.liftIoc 1 0 U

/-- Multiplicatively, this is exactly W(s)=s U(s⁴). -/
def fourthRootCircleLift {r : ℕ} (U : ℝ → Circulation.Mat r)
    (t : UnitCircle) : Circulation.Mat r :=
  fourier 1 t • intervalCircleLift U (4 • t)

def hermitianRealPart {r : ℕ} (X : Circulation.Mat r) : Circulation.Mat r :=
  (1 / 2 : ℂ) • (X + Xᴴ)

def hermitianImagPart {r : ℕ} (X : Circulation.Mat r) : Circulation.Mat r :=
  (-Complex.I / 2) • (X - Xᴴ)

def fourthRootCircleA {r : ℕ} (U : ℝ → Circulation.Mat r)
    (t : UnitCircle) : Circulation.Mat r :=
  hermitianRealPart (fourthRootCircleLift U t) + hermitianImagPart (fourthRootCircleLift U t)

def fourthRootCircleB {r : ℕ} (U : ℝ → Circulation.Mat r)
    (t : UnitCircle) : Circulation.Mat r :=
  hermitianRealPart (fourthRootCircleLift U t) - hermitianImagPart (fourthRootCircleLift U t)

end
end CGLMPBounds.Hardy
