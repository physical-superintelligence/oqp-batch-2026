module

public import CausalNonpurifiability.Definitions.ProcessCore
public import CausalNonpurifiability.StatementCore

@[expose] public section


/-! Exact original statement definitions; all theorem providers remain in their original modules. -/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix
open scoped Kronecker ComplexOrder

section Ball
variable (D : Ports)

/-- The ball radius `1/(300 m n)` (`eq:ball`). -/
noncomputable def ballRadius : ℂ := 1 / (300 * D.m * D.n)

/-- The lower bound `1/(150 m n)` of `eq:ball-fullrank`. -/
noncomputable def lowerBound : ℂ := 1 / (150 * D.m * D.n)

/-- The closed relative ball `eq:ball` in PSD form: `H ∈ L_V`, `Tr H = 0`,
`r I + H ≥ 0`, `r I - H ≥ 0`. For Hermitian `H` the last two conditions say `‖H‖_∞ ≤ r`
(`Matrix.toEuclideanCLM` operator norm); that equivalence is left to a later lemma. -/
def InBall (H : PMat D) : Prop :=
  InLV D H ∧ H.trace = 0 ∧ (ballRadius D • (1 : PMat D) + H).PosSemidef ∧
    (ballRadius D • (1 : PMat D) - H).PosSemidef

end Ball

/-- Atomic numeral witnesses for the exact ball inequality. They are selected
only around that statement and its proof, so literal proposition data retains
the same proof constants as the theorem type. No global instances are added. -/
theorem ballNegativeExact_atLeastTwo49 : Nat.AtLeastTwo 49 := inferInstance

theorem ballNegativeExact_atLeastTwo500 : Nat.AtLeastTwo 500 := inferInstance

theorem ballNegativeExact_atLeastTwo10 : Nat.AtLeastTwo 10 := inferInstance

theorem ballNegativeExact_atLeastTwo75 : Nat.AtLeastTwo 75 := inferInstance

end CausalNonpurifiability
