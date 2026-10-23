module

public import CausalNonpurifiability.Linear.Indices
public import CausalNonpurifiability.Data.Local

@[expose] public section


/-! Exact original statement definitions; all theorem providers remain in their original modules. -/

set_option autoImplicit false

namespace CausalNonpurifiability

/-- The four-qubit process `W_q = W_0|_{m=d=n=e=2}` (`eq:qubit`), lifted from the rational
construction `W0 2 2 2 2` (`eq:centers`) to a complex process matrix. -/
noncomputable def Wq : PMat qubits := toC (W0 2 2 2 2)

/-- The centre `W_c = (99/100) W_0 + (1/100) I/(mn)` of the ball `eq:ball` (`eq:centers`), as
a complex operator on `A_I A_O B_I B_O`. -/
noncomputable def WcC (D : Ports) : PMat D := toC (Wc D.m D.d D.n D.e)

end CausalNonpurifiability
