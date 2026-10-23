module

public import CausalNonpurifiability.Data.QubitCore
public import CausalNonpurifiability.Data.Local

@[expose] public section


/-!
# `CausalNonpurifiability.Data.Qubit`

Independent entrywise specification of $80 W_q$ on four qubit ports
(Appendix C, with the zero-based flat index `j = 8α + 4o + 2β + t`) and its equality
with the tensor construction `W0 2 2 2 2` of `CausalNonpurifiability.Data.Local` under the flat
reindexing `((α,o),(β,t)) ↦ 8α + 4o + 2β + t`.

The entrywise matrix is defined from the digits of `j` alone; nothing from the
Kronecker construction enters. `wq_entries_eq_pauli` is the comparison theorem
(an independent entrywise construction, compared with the tensor construction; the entries are
those of Appendix C). The equivalence `qubitFlat` is local to this file; the
canonical `labFlat : LabIndex qubits ≃ Fin 16` of `Linear/Indices.lean` is definitionally the same map,
so the swap is a one-line change of the statement.

Manuscript anchors: `eq:qubit`; the entries of `80 W_q` and the flat index of Appendix C.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix

/-! ### Digits of the flat index `j = 8α + 4o + 2β + t` -/

/-! ### Regression data (the diagonal of `tab:diagonal` and the off-diagonal entries of Appendix C) -/

theorem wq80_diagonal_list : (List.ofFn fun j : Fin 16 => Wq80 j j)
    = [49, 49, 11, 11, 41, 41, 19, 19, 19, 19, 1, 1, 11, 11, 9, 9] := by decide +kernel

theorem wq80_offDiagonal_entries : Wq80 0 2 = 4 ∧ Wq80 1 3 = -4 ∧ Wq80 4 6 = 4 ∧ Wq80 5 7 = -4 ∧
    Wq80 8 10 = -4 ∧ Wq80 9 11 = 4 ∧ Wq80 12 14 = -4 ∧ Wq80 13 15 = 4 := by decide +kernel

/-- Both symmetric off-diagonal entries are specified. -/
theorem wq80_offDiagonal_symmetric_entries : Wq80 2 0 = 4 ∧ Wq80 3 1 = -4 ∧ Wq80 14 12 = -4 ∧ Wq80 15 13 = 4 := by decide +kernel

/-- Every entry outside the diagonal and the `β`-flip pairs vanishes: 16 + 16 nonzero entries. -/
theorem wq80_nonzero_card : ((Finset.univ : Finset (Fin 16 × Fin 16)).filter fun p => Wq80 p.1 p.2 ≠ 0).card = 32 := by
  decide +kernel

theorem wq80_transpose : Wq80ᵀ = Wq80 := by decide +kernel

/-! ### Flat reindexing of the qubit lab index -/

@[simp] lemma qubitFlat_apply (x : Lab 2 2 2 2) :
    (qubitFlat x).val = 8 * x.1.1.val + 4 * x.1.2.val + 2 * x.2.1.val + x.2.2.val := rfl

/-! ### The comparison theorem -/

/-- The entrywise matrix of Appendix C is the tensor construction `W0` at
`m = d = n = e = 2` (`eq:qubit`), transported along `qubitFlat`. -/
theorem wq_entries_eq_pauli : WqEntries = Matrix.reindex qubitFlat qubitFlat (W0 2 2 2 2) := by
  decide +kernel

/-- Inverse form: the qubit tensor construction is the entrywise matrix pulled back. -/
theorem w0_qubit_eq_wq : W0 2 2 2 2 = Matrix.reindex qubitFlat.symm qubitFlat.symm WqEntries := by
  rw [wq_entries_eq_pauli]
  ext i j
  simp [reindex_apply, submatrix_apply]

/-- `Tr W_q = 4` (`eq:qubit-minimum`). -/
theorem trace_wq : trace WqEntries = 4 := by decide +kernel

end CausalNonpurifiability
