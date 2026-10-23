module

public import CausalNonpurifiability.Definitions.CausalProcessCore
public import CausalNonpurifiability.Definitions.Instruments

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

end

end CausalNonpurifiability
