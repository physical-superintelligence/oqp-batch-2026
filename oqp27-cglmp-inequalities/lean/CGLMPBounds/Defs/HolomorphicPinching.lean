module

public import CGLMPBounds.Defs.PositivePinching

@[expose] public section


/-! Literal holomorphic trace and strip in source C.5. The root sum retains
algebraic multiplicities, including defective eigenvalues. For holomorphic f
it is the trace of f(A), but that functional-calculus identification and the
pinching identity are theorem obligations, not parts of the definitions. -/

namespace CGLMPBounds
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def openVerticalUnitStrip : Set ℂ := {z : ℂ | |z.re| < 1}

def normalizedSpectralTrace (f : ℂ → ℂ) (A : Matrix ι ι ℂ) : ℂ :=
  (A.charpoly.roots.map f).sum / (Fintype.card ι : ℂ)

end
end CGLMPBounds
