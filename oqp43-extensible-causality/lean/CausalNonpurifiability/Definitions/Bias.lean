module

public import CausalNonpurifiability.Data.Local

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.Bias`

Statement vocabulary for `subsec:bias`: the operator of `eq:centers` and the
operator `C` of `eq:C-def` when the biased states `θ_m`, `θ_n` are replaced by the unbiased
states `P_m/2`, `P_n/2`.
-/

set_option autoImplicit false

open Matrix
open scoped Kronecker

namespace CausalNonpurifiability

variable (m d n e : ℕ)

/-- `eq:centers` with `θ_m ⊗ θ_n` replaced by `(P_m/2) ⊗ (P_n/2)`:
`Q_{(P_m/2) ⊗ (P_n/2)} + (G_A + G_B)/20`. -/
def W0unbiased : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  Qembed d e (((1 / 2 : ℚ) • P m) ⊗ₖ ((1 / 2 : ℚ) • P n)) +
    (1 / 20 : ℚ) • (GA m d n e + GB m d n e)

/-- `eq:C-def` with the unbiased states: `2C = (P_m/2) ⊗ (P_n/2) - (P_m ⊗ P_n)/10`. -/
def Cunbiased : Matrix (Fin m × Fin n) (Fin m × Fin n) ℚ :=
  (1 / 2 : ℚ) • (((1 / 2 : ℚ) • P m) ⊗ₖ ((1 / 2 : ℚ) • P n) - (1 / 10 : ℚ) • (P m ⊗ₖ P n))

end CausalNonpurifiability
