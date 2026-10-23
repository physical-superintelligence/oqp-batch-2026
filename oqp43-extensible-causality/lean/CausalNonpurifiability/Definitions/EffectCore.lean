module

public import Mathlib

@[expose] public section


/-! Exact effect predicate separated from its proof provider for trusted statements. -/

set_option autoImplicit false
open scoped ComplexOrder
namespace CausalNonpurifiability
variable {ι : Type}

/-- An *effect* on the finite index type `ι`: `0 ≤ F ≤ 1` in the Loewner order,
recorded as the two PSD conditions `F ≥ 0` and `1 - F ≥ 0`.  These are the
effects `E_0, E_1, H_0, H_1` of Lemma 5.2 (`lem:SOS`: "The two effects `E_0` and
`E_1` may be arbitrary, and so may `H_0` and `H_1`"; no projectivity, no commutation between
same-side effects). -/
def Effect [DecidableEq ι] (F : Matrix ι ι ℂ) : Prop :=
  F.PosSemidef ∧ (1 - F).PosSemidef


end CausalNonpurifiability
