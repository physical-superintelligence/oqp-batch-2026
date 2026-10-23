module

public import CausalNonpurifiability.Certificates.Qubit
public import CausalNonpurifiability.Definitions.OCB

@[expose] public section


/-!
# `CausalNonpurifiability.OCB`

Appendix C: the witness gives `Tr(S_0 W_OCB) = 10 - 8√2 < 0`. The rational traces
`Tr S_0 = 40` and `Tr(S_0 (IZZI + ZIXZ)) = -64` are checked by kernel evaluation.
-/

set_option autoImplicit false

open Matrix

namespace CausalNonpurifiability

theorem trace_S0_qubit : trace (S0 2 2 2 2 * kron4 1 1 1 1) = 40 := by decide +kernel

theorem trace_S0_OCB_terms :
    trace (S0 2 2 2 2 * (kron4 1 !![1, 0; 0, -1] !![1, 0; 0, -1] 1 +
      kron4 !![1, 0; 0, -1] 1 !![0, 1; 1, 0] !![1, 0; 0, -1])) = -64 := by decide +kernel

/-- **Appendix C**: `Tr(S_0 W_OCB) = 10 - 8√2 < 0`. -/
theorem appC_OCB :
    (toC (S0 2 2 2 2) * WOCB).trace = ((10 - 8 * Real.sqrt 2 : ℝ) : ℂ) ∧
      10 - 8 * Real.sqrt 2 < 0 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := by positivity
  have k : (1 / 4 : ℝ) * 40 + 1 / (4 * Real.sqrt 2) * (-64) = 10 - 8 * Real.sqrt 2 := by
    have k2 : (1 : ℝ) / (4 * Real.sqrt 2) * (-64) = -8 * Real.sqrt 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_eq_iff (by positivity)]
      linear_combination 32 * hs
    rw [k2]
    ring
  refine ⟨?_, by nlinarith [hs, hpos]⟩
  rw [WOCB, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, ← Matrix.map_mul, ← Matrix.map_mul, trace_toC, trace_toC, trace_S0_qubit,
    trace_S0_OCB_terms, ← k]
  push_cast
  ring

end CausalNonpurifiability
