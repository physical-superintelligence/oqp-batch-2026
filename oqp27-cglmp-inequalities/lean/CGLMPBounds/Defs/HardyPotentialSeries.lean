module

public import CGLMPBounds.Defs.HardyPotential

@[expose] public section


/-! Explicit auxiliary series for the C.14 boundary analysis. Identification
with the source's actual double primitive is a separate theorem target. -/

namespace CGLMPBounds.Hardy
noncomputable section

def hardyOddDilog (q : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * q ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℂ) ^ 2

def hardyUpperPotential (z : ℂ) : ℂ :=
  -Complex.I * z + (8 / (Real.pi : ℂ) ^ 2) *
    hardyOddDilog (Complex.exp (Complex.I * Real.pi * z / 2))

end
end CGLMPBounds.Hardy
