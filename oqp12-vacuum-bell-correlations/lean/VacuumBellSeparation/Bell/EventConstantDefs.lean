module

public import VacuumBellSeparation.Bell.Defs

@[expose] public section


/-!
# The event comparison constants `K_{r,±}` (definitions only)

Equation (3.1) (`eq:K`) of the manuscript defines, for `r > 1`,

`K_{r,+} = sup_{E,P} ω(EP)^r / (ω(E)ω(P))^{r-1}`,
`K_{r,-} = sup_{E,P} (ω(E)ω(P))^r / ω(EP)^{r-1}`,

the suprema ranging over local projections with positive product of marginals, a positive
numerator with zero denominator giving `+∞`.  Here they are `eventConstPlus` and
`eventConstMinus`, valued in `ℝ≥0∞` (in `ℝ≥0∞`, `x / 0 = ⊤` for `x ≠ 0`).

This module contains definitions only.
-/

open scoped ENNReal

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The event comparison constant `K_{r,+}` of (3.1). -/
noncomputable def eventConstPlus (ω : State H) (𝔄 𝔅 : VonNeumannAlgebra H) (r : ℝ) : ℝ≥0∞ :=
  ⨆ E ∈ projections 𝔄, ⨆ P ∈ projections 𝔅, ⨆ (_ : 0 < (ω E).re * (ω P).re),
    ENNReal.ofReal ((ω (E * P)).re ^ r / ((ω E).re * (ω P).re) ^ (r - 1))

/-- The event comparison constant `K_{r,-}` of (3.1); the quotient is taken in `ℝ≥0∞`, so a
positive numerator over a zero denominator is `⊤`. -/
noncomputable def eventConstMinus (ω : State H) (𝔄 𝔅 : VonNeumannAlgebra H) (r : ℝ) : ℝ≥0∞ :=
  ⨆ E ∈ projections 𝔄, ⨆ P ∈ projections 𝔅, ⨆ (_ : 0 < (ω E).re * (ω P).re),
    ENNReal.ofReal (((ω E).re * (ω P).re) ^ r) / ENNReal.ofReal ((ω (E * P)).re ^ (r - 1))

end VacuumBellSeparation
