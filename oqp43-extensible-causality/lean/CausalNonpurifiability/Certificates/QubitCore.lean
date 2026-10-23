module

public import CausalNonpurifiability.Data.Local

@[expose] public section


/-! Original block entries, Gram data and output partial trace. All certificate
identities and target-provider proofs stay in Certificates.Qubit. -/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix
open scoped Kronecker ComplexOrder

/-- Leading diagonal entry `a(α, o)` of the `B_I` block of `80 W_q` at Alice input `α` and
`Z_d^+`-eigenvalue `(-1)^o`: `49, 41, 19, 11`. -/
def blockA (α o : ℕ) : ℚ :=
  if α = 0 then (if o = 0 then 49 else 41) else (if o = 0 then 19 else 11)

/-- Trailing diagonal entry `b(α, o)`: `11, 19, 1, 9`. -/
def blockB (α o : ℕ) : ℚ :=
  if α = 0 then (if o = 0 then 11 else 19) else (if o = 0 then 1 else 9)

/-- `K` in vertex order `A0, A1, B0, B1` (`eq:K`). -/
def Kmat : Matrix (Fin 4) (Fin 4) ℚ :=
  (1 / 160 : ℚ) • !![44, 0, -37, -7; 0, 4, -7, 3; -37, -7, 44, 0; -7, 3, 0, 4]

def bvec : Fin 4 → ℚ := ![1, 0, -1, 0]
def uvec : Fin 4 → ℚ := ![7, 1, -7, -1]
def vvec : Fin 4 → ℚ := ![-1, 1, -1, 1]

section ActualInput
variable {m d n e : ℕ}

/-- Rational partial trace over both outputs `A_O, B_O` (entry rule of `sec:verification`). -/
def ptrOut (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℚ :=
  of fun x y => ∑ o, ∑ t, T ((x.1, o), (x.2, t)) ((y.1, o), (y.2, t))

end ActualInput

end CausalNonpurifiability
