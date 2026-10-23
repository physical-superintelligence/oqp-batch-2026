module

public import CausalNonpurifiability.Definitions.InstrumentsCore

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.CausalProcess`

The Born rule `eq:born` without additional systems, and causal processes (Definition 2.6, second
sentence: "A process is causal if every distribution `eq:born` that it generates is causal").
-/

set_option autoImplicit false

open scoped Kronecker

namespace CausalNonpurifiability

noncomputable section

variable (D : Ports) {X Y A B : Type} [Fintype A] [Fintype B]

/-- The Born rule `eq:born`: `p(a,b|x,y) = Re Tr[W (M_{a|x} ⊗ N_{b|y})]`. -/
def born (W : PMat D) (M : Instrument (Fin D.m) (Fin D.d) X A)
    (N : Instrument (Fin D.n) (Fin D.e) Y B) : Prob X Y A B :=
  fun x y a b => ((W * (M.elem x a ⊗ₖ N.elem y b)).trace).re

/-- **Causal process** (Definition 2.6, second sentence): a process all of whose distributions
`eq:born`, for all instruments with finite sets of settings and outcomes, are causal. -/
def CausalProcess (W : PMat D) : Prop :=
  Valid D W ∧
    ∀ (nx ny na nb : ℕ) (M : Instrument (Fin D.m) (Fin D.d) (Fin (nx + 1)) (Fin (na + 1)))
      (N : Instrument (Fin D.n) (Fin D.e) (Fin (ny + 1)) (Fin (nb + 1))),
      Causal (born D W M N)

end

end CausalNonpurifiability
