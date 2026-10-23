module

public import CGLMPBounds.Defs.CGLMP

@[expose] public section


/-!
# The projective CGLMP value `I_d^F` (definition)

Supplement, Theorem A.1, equation (A.1) (Letter, eq. (3)): for `d ≥ 2`,
`I_d^F := 4/(d(d-1)) Σ_{h=1}^{d-1} (d - h) sec(π h/(2d))`.

This file contains definitions only (no theorems); it belongs to the statement dependency closure.
-/

namespace CGLMPBounds

noncomputable section

/-- The Fourier value (A.1), `I_d^F = 4/(d(d-1)) Σ_{h=1}^{d-1} (d - h) sec(π h/(2d))`, with
`sec t = 1 / cos t`; `Finset.Ico 1 d = {1, …, d-1}`. -/
def cglmpFourierValue (d : ℕ) : ℝ :=
  4 / ((d : ℝ) * ((d : ℝ) - 1)) *
    ∑ h ∈ Finset.Ico 1 d, ((d : ℝ) - h) / Real.cos (Real.pi * h / (2 * d))

end

end CGLMPBounds
