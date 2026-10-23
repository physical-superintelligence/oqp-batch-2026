module

public import CGLMPBounds.Defs.Quantum

@[expose] public section


/-! The literal squared Frobenius norm used by the Appendix E estimates.
This pure definition contains no positivity or commutator-bound assumption. -/

open Matrix
open scoped ComplexOrder

namespace CGLMPBounds

noncomputable section

variable {n : ℕ}

/-- Squared Frobenius norm, expressed by the real trace of `X†X`. -/
def deficitHSSq (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := (Matrix.trace (Xᴴ * X)).re

end

end CGLMPBounds
