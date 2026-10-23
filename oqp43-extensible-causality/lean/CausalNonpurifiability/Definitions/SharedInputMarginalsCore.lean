module

public import CausalNonpurifiability.Linear.PartialTrace

@[expose] public section


/-! Exact shared-input marginal definitions, separated from rectangle proofs. -/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace CausalNonpurifiability

noncomputable section

section Reduced

variable {RA RB : Type} [Fintype RA] [Fintype RB]

/-- Alice's reduced ancilla state `σ^{R_A} = Tr_{R_B} σ` (`eq:endpoints`). -/
def sigmaA (σ : Op (RA × RB)) : Op RA := ptraceOut σ

/-- Bob's reduced ancilla state `σ^{R_B} = Tr_{R_A} σ` (`eq:endpoints`). -/
def sigmaB (σ : Op (RA × RB)) : Op RB := ptraceFst σ

end Reduced
end
end CausalNonpurifiability
