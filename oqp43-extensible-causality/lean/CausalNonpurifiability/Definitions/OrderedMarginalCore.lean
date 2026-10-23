module

public import CausalNonpurifiability.Definitions.ProcessCore

@[expose] public section


/-! Exact historical statement vocabulary; surrounding proof declarations remain in their original owners. -/

set_option autoImplicit false

namespace CausalNonpurifiability

variable (D : Ports)

/-- The `A_O`-stripped operator `T̂ = Tr_{A_O} T / d` on `A_I B_I B_O`. -/
noncomputable def hatBA (T : PMat D) : Op (Fin D.m × (Fin D.n × Fin D.e)) :=
  ((D.d : ℂ))⁻¹ • ptraceOut (Matrix.reindex (eqAO _ _ _ _) (eqAO _ _ _ _) T)

end CausalNonpurifiability
