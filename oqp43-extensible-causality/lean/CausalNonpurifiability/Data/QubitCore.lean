module

public import CausalNonpurifiability.Data.Local

@[expose] public section


/-! Original qubit entries and fixed flat-index equivalence, including all
bounds and inverse proofs. The entry/tensor comparison stays in Data.Qubit. -/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix

/-- `α` digit (Alice input) of `j`. -/
def qα (j : Fin 16) : ℕ := j.val / 8
/-- `o` digit (Alice output) of `j`. -/
def qo (j : Fin 16) : ℕ := j.val / 4 % 2
/-- `β` digit (Bob input) of `j`. -/
def qβ (j : Fin 16) : ℕ := j.val / 2 % 2
/-- `t` digit (Bob output) of `j`. -/
def qt (j : Fin 16) : ℕ := j.val % 2

/-- `80 W_q` by the entry rules of Appendix C: diagonal
`5(3-2α)(3-2β) + 4(-1)^{o+β}`; the two symmetric off-diagonal entries between `j(α,o,β,t)`
and `j(α,o,1-β,t)` equal `4(-1)^{α+t}`; all other entries vanish. -/
def Wq80 : Matrix (Fin 16) (Fin 16) ℚ :=
  of fun j k =>
    if j = k then
      5 * (3 - 2 * (qα j : ℚ)) * (3 - 2 * (qβ j : ℚ)) + 4 * (-1) ^ (qo j + qβ j)
    else if qα j = qα k ∧ qo j = qo k ∧ qt j = qt k then
      4 * (-1) ^ (qα j + qt j)
    else 0

/-- `W_q = (80 W_q)/80` (`eq:qubit`; Appendix C). -/
def WqEntries : Matrix (Fin 16) (Fin 16) ℚ := (1 / 80 : ℚ) • Wq80

/-- `((α,o),(β,t)) ↦ 8α + 4o + 2β + t` (the flat index `8i+4o+2j+t` of Appendix C). -/
def qubitFlat : Lab 2 2 2 2 ≃ Fin 16 where
  toFun x := ⟨8 * x.1.1.val + 4 * x.1.2.val + 2 * x.2.1.val + x.2.2.val, by omega⟩
  invFun j := ((⟨j.val / 8, by omega⟩, ⟨j.val / 4 % 2, by omega⟩),
    (⟨j.val / 2 % 2, by omega⟩, ⟨j.val % 2, by omega⟩))
  left_inv x := by revert x; decide
  right_inv j := by revert j; decide

end CausalNonpurifiability
