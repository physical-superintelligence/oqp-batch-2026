module

public import CausalNonpurifiability.Linear.Replacement

@[expose] public section


/-! The original three homogeneous process equations, separated from the
channel-normalization proof. No Hermiticity or normalization premise is added. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Kronecker Matrix ComplexOrder

namespace CausalNonpurifiability

noncomputable section

section Generic
variable {A O B T : Type} [Fintype A] [Fintype O] [Fintype B] [Fintype T]
  [DecidableEq A] [DecidableEq O] [DecidableEq B] [DecidableEq T]

/-- The three homogeneous equations of `eq:LV`, without the Hermiticity clause of `GenLV`. -/
def LVEquations (W : Op (LabIdx A O B T)) : Prop :=
  R_BIBO W - R_AO (R_BIBO W) = 0 ∧ R_AIAO W - R_BO (R_AIAO W) = 0 ∧
    W - R_AO W - R_BO W + R_AO (R_BO W) = 0

end Generic

end
end CausalNonpurifiability
