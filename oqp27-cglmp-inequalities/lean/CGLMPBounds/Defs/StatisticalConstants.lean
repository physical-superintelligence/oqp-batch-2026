module

public import Mathlib

@[expose] public section


/-! Literal Fourier local weight and base-two statistical ceiling.
Definitions only; relocated without changing the formulas or names. -/

namespace CGLMPBounds
noncomputable section

/-- The local weight a_d = 2 / (d² sin²(3π/(4d))) of Lemma F.1. -/
def localWeight (d : ℕ) : ℝ :=
  2 / ((d : ℝ) ^ 2 * Real.sin (3 * Real.pi / (4 * (d : ℝ))) ^ 2)

/-- The uniform-input ceiling `c_KL = log₂(4/3)` of Theorem F.2. -/
def cKL : ℝ := Real.logb 2 (4 / 3)

end
end CGLMPBounds
