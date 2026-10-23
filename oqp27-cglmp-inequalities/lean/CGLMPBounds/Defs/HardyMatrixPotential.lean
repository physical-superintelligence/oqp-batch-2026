module

public import CGLMPBounds.Defs.HardyPotential
public import Mathlib.Analysis.Matrix.Order

@[expose] public section


/-! Literal matrix potential and normalized trace of matrix absolute value
in C.15–C.16. The root sum retains algebraic multiplicities. Matrix absolute
value is the actual positive square root of A†A supplied by CFC, not a
spectral bound or a positivity premise. -/

namespace CGLMPBounds
noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixHardyPotential (A : Matrix ι ι ℂ) : ℝ :=
  (normalizedSpectralTrace Hardy.hardyStripPotential A).re

def normalizedMatrixAbsTrace (A : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (CFC.abs A)).re / (Fintype.card ι : ℝ)

end
end CGLMPBounds
