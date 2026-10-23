module

public import CausalNonpurifiability.Definitions.ProcessCore

@[expose] public section


/-! Exact historical statement vocabulary; surrounding proof declarations remain in their original owners. -/

set_option autoImplicit false

namespace CausalNonpurifiability

/-- Definition 2.4: `W` is a convex combination `q W_A + (1 - q) W_B` of a process `W_A` of order
`A ≺ B` and a process `W_B` of order `B ≺ A`, with `0 ≤ q ≤ 1`. -/
def CausallySeparableConvex (D : Ports) (W : PMat D) : Prop :=
  ∃ (q : ℝ) (WA WB : PMat D), 0 ≤ q ∧ q ≤ 1 ∧ Valid D WA ∧ OrderedAB D WA ∧
    Valid D WB ∧ OrderedBA D WB ∧ W = (q : ℂ) • WA + ((1 - q : ℝ) : ℂ) • WB

end CausalNonpurifiability
