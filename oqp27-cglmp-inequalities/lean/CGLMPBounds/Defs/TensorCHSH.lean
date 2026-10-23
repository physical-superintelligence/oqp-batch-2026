module

public import Mathlib

@[expose] public section


/-!
# Tensor CHSH error counts (definition)

Appendix F.2 of the manuscript: each party outputs an `m`-bit string and, for inputs `x y`,
`K_{xy}(a,b) = #{j : a_j ⊕ b_j ≠ x·y}` counts the coordinates violating the CHSH parity.
This file contains definitions only.
-/

namespace CGLMPBounds.TensorCHSH

/-- `errCount x y s t` is the CHSH error count `K_{xy}(s,t) = #{j : s_j ⊕ t_j ≠ x·y}`. -/
def errCount {m : ℕ} (x y : Fin 2) (s t : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun j : Fin m => xor (s j) (t j) ≠ (decide (x = 1) && decide (y = 1))).card

end CGLMPBounds.TensorCHSH
