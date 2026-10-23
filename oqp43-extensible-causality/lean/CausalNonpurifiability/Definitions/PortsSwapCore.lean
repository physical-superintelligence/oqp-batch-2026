module

public import CausalNonpurifiability.Linear.Indices

@[expose] public section


/-! Exact historical statement vocabulary; surrounding proof declarations remain in their original owners. -/

set_option autoImplicit false

open scoped Kronecker ComplexOrder Matrix

namespace CausalNonpurifiability

noncomputable section

/-- Exchange the two parties: `(m, d, n, e) ↦ (n, e, m, d)` (reducible, so that `D.swap.m` unfolds
to `D.n`, …). -/
abbrev Ports.swap (D : Ports) : Ports := ⟨D.n, D.e, D.m, D.d, ⟨D.n_pos, D.e_pos, D.m_pos, D.d_pos⟩⟩

end

end CausalNonpurifiability
