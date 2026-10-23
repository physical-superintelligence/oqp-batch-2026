module

public import CausalNonpurifiability.Linear.Indices

@[expose] public section


/-! The original Gram-form family for a fixed global matrix and two past
vectors. Positivity, normalization and homogeneous process equations remain
separate theorems in Purification.Family. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

noncomputable section

section Process

variable {D : Ports} {p f : ℕ}
  (U : Matrix (Fin (f + 1) × (Fin D.m × Fin D.n)) (Fin (p + 1) × (Fin D.d × Fin D.e)) ℂ)

/-- `W_τ` for `τ = |u⟩⟨v|`, in Gram form (Step 2 of Appendix A). -/
def procV (u v : Fin (p + 1) → ℂ) : PMat D :=
  fun l l' => ∑ z, (∑ x, U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) * u x) *
    star (∑ x', U (z, (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2)) * v x')

end Process

end
end CausalNonpurifiability
