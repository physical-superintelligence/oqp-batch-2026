module

public import CGLMPBounds.Defs.Scenario

@[expose] public section


/-!
# The CGLMP functional (definitions)

The normalisation of the Collins–Gisin–Linden–Massar–Popescu functional used by the manuscript,
equation (B.1) of Appendix B (equation (1) of the Letter):

`r₀₀ = [a - b]_d`, `r₁₀ = [b - a]_d`, `r₁₁ = [a - b]_d`, `r₀₁ = [b - a - 1]_d`,
`S_d(q) = ∑_{x,y} E_q r_{xy}`, `I_d(q) = 4 - 2 S_d(q) / (d - 1)`.

Outcomes are elements of `ZMod d`; `[u]_d ∈ {0, …, d-1}` is `ZMod.val`.
This file contains definitions only.
-/

namespace CGLMPBounds

noncomputable section

/-- The oriented residual `r_{xy}(a,b) ∈ {0, …, d-1}` of (B.1):
`r₀₀ = [a-b]_d`, `r₁₁ = [a-b]_d`, `r₁₀ = [b-a]_d`, `r₀₁ = [b-a-1]_d`. -/
def residual (d : ℕ) (x y : Fin 2) (a b : ZMod d) : ℕ :=
  if x = y then (a - b).val else if x = 1 then (b - a).val else (b - a - 1).val

/-- `S_d(q) = ∑_{x,y} E_q r_{xy}`, equation (B.1). -/
def cglmpS (d : ℕ) [NeZero d] (q : Table (ZMod d) (ZMod d)) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, (residual d x y a b : ℝ) * q x y a b

/-- The CGLMP value `I_d(q) = 4 - 2 S_d(q) / (d - 1)`, equation (B.1). -/
def cglmp (d : ℕ) [NeZero d] (q : Table (ZMod d) (ZMod d)) : ℝ :=
  4 - 2 * cglmpS d q / ((d : ℝ) - 1)

end

end CGLMPBounds
