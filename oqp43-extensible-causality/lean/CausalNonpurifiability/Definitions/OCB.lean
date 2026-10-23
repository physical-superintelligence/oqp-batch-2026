module

public import CausalNonpurifiability.Data.Local

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.OCB`

The process `W_OCB = (IIII + (IZZI + ZIXZ)/√2)/4` of Oreshkov, Costa and Brukner on four qubits
(manuscript introduction and Appendix C), in the order `A_I A_O B_I B_O`, with
`Z = diag(1, -1)` and `X = [[0, 1], [1, 0]]`.
-/

set_option autoImplicit false

open Matrix

namespace CausalNonpurifiability

/-- `W_OCB = (IIII + (IZZI + ZIXZ)/√2)/4`. -/
noncomputable def WOCB : Matrix (Lab 2 2 2 2) (Lab 2 2 2 2) ℂ :=
  ((1 / 4 : ℝ) : ℂ) • toC (kron4 1 1 1 1) +
    ((1 / (4 * Real.sqrt 2) : ℝ) : ℂ) •
      toC (kron4 1 !![1, 0; 0, -1] !![1, 0; 0, -1] 1 +
        kron4 !![1, 0; 0, -1] 1 !![0, 1; 1, 0] !![1, 0; 0, -1])

end CausalNonpurifiability
