module

public import VacuumBellSeparation.Probability.Exponents

@[expose] public section


/-!
# Statement seed extracted from Constants/Parameters

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

namespace VacuumBellSeparation

/-- `Λ₀ = 2¹⁵` of (7.10). -/
def Lambda0 : ℝ := 2 ^ 15

/-- `θ = 1/(4Λ₀)` of (7.10). -/
noncomputable def theta : ℝ := 1 / (4 * Lambda0)

/-- `a = θ/2` of (7.10). -/
noncomputable def aRev : ℝ := theta / 2

/-- `γ = 2(1 - θ)` of (7.10). -/
noncomputable def gammaRev : ℝ := 2 * (1 - theta)

/-- `r₋ = 1/(1 - a)` of (8.1). -/
noncomputable def rMinus : ℝ := 1 / (1 - aRev)

/-- `r₊ = 2²⁰` of (8.1) (the manuscript writes `r₊ = ⌈4/a⌉ = 2²⁰`; see `four_div_aRev`). -/
def rPlus : ℝ := 2 ^ 20


end VacuumBellSeparation
