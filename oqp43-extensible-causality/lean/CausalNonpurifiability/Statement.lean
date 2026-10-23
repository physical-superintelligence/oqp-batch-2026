module

public import CausalNonpurifiability.StatementCore
public import CausalNonpurifiability.Definitions.Process
public import CausalNonpurifiability.Data.Local

@[expose] public section


/-!
# `CausalNonpurifiability.Statement` — objects named in the public endpoints

This module holds only the definitions that appear in the *statements* of the
public theorems and in the trusted Comparator challenges, so that a challenge
can import the statement vocabulary without importing any proof module.

* `Wq` — the four-qubit process `W_q = W_0|_{m=d=n=e=2}` (`eq:qubit`), as a
  complex process matrix on `LabIndex qubits` (tensor order `A_I, A_O, B_I, B_O`).
* `WcC` — the centre `W_c` of the ball `eq:ball` (`eq:centers`), as a complex operator.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

end CausalNonpurifiability
