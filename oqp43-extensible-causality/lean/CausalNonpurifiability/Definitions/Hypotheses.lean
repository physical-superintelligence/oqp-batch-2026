module

public import CausalNonpurifiability.Definitions.Process
public import CausalNonpurifiability.Definitions.Purity

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.Hypotheses`

Named hypotheses passed to some library statements as explicit theorem parameters.
They are `def`s of type `Prop`, never axioms. `PurificationNecessity` is proved as Theorem 6.1,
`purification_necessity` (`Purification/Necessity.lean`); there is no literature axiom.

Manuscript anchors: `eq:purcs` (`Pur₂ ⊆ CS₂`), §6.1.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

/-- Purification necessity: every valid, purifiable bipartite process with
trivial original past and future is causally separable (`eq:purcs`).
Published as Yokojima–Quintino–Soeda–Murao, Cor. 1 (arXiv:2003.05682) and
Barrett–Lorenz–Oreshkov, Thm. 3; re-proved in manuscript §6.1. -/
def PurificationNecessity : Prop :=
  ∀ (D : Ports) (W : PMat D), Valid D W → Purifiable D W → CausallySeparable D W

end CausalNonpurifiability
