module

public import CausalNonpurifiability

/-!
# Proofs of the statements of `Challenge.lean`

Each theorem repeats its statement in `Challenge.lean` verbatim and is proved from the library
`CausalNonpurifiability`. Comparator checks that the statements agree and that the proofs use
only the axioms `propext`, `Quot.sound` and `Classical.choice`.
-/

public section

set_option autoImplicit false

open scoped ComplexOrder Kronecker Matrix

namespace CausalNonpurifiability.OQP43

theorem not_all_extensiblyCausal_purifiable :
    ∃ W : PMat qubits, ExtensiblyCausal qubits W ∧ ¬ Purifiable qubits W :=
  CausalNonpurifiability.oqp43_negative

theorem theorem_1_1 :
    Valid qubits Wq ∧ Wq.PosDef ∧ ExtensiblyCausal qubits Wq ∧ ¬ CausallySeparable qubits Wq ∧
      ¬ Purifiable qubits Wq :=
  CausalNonpurifiability.theorem_intro

theorem wq_pauli_form :
    Wq = toC (W0 2 2 2 2) ∧
      W0 2 2 2 2 = (1 / 80 : ℚ) • ((20 : ℚ) • kron4 1 1 1 1 +
        (10 : ℚ) • kron4 !![1, 0; 0, -1] 1 1 1 + (10 : ℚ) • kron4 1 1 !![1, 0; 0, -1] 1 +
        (5 : ℚ) • kron4 !![1, 0; 0, -1] 1 !![1, 0; 0, -1] 1 +
        (4 : ℚ) • kron4 1 !![1, 0; 0, -1] !![1, 0; 0, -1] 1 +
        (4 : ℚ) • kron4 !![1, 0; 0, -1] 1 !![0, 1; 1, 0] !![1, 0; 0, -1]) :=
  CausalNonpurifiability.eq_qubit_pauli

theorem purifiable_iff_transpose_formula (D : Ports) (W : PMat D) :
    Purifiable D W ↔
      ∃ (p f : ℕ) (S : HigherOp D p f), Pure D S ∧ (reducePastFuture D S)ᵀ = W :=
  CausalNonpurifiability.purifiable_iff_transpose_convention D W

theorem valid_iff_channels_normalized (D : Ports) {W : PMat D} (hW : W.PosSemidef) :
    Valid D W ↔ ∀ (Mt : Op (Fin D.m × Fin D.d)) (Nt : Op (Fin D.n × Fin D.e)),
      Mt.PosSemidef → ptraceOut Mt = 1 → Nt.PosSemidef → ptraceOut Nt = 1 →
      (W * (Mt ⊗ₖ Nt)).trace = 1 :=
  CausalNonpurifiability.valid_iff_channel_normalization D hW

theorem white_process_purifiable (D : Ports) :
    Valid D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) ∧
      OrderedAB D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) ∧
      OrderedBA D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) ∧
      Purifiable D ((1 / ((D.m : ℂ) * D.n)) • (1 : PMat D)) :=
  CausalNonpurifiability.white_process D

theorem swap_table_not_causal :
    ¬ Causal (fun (x y a b : Fin 2) => if a = y ∧ b = x then (1 : ℝ) else 0) :=
  CausalNonpurifiability.not_causal_swap

theorem ocb_process_not_extensiblyCausal :
    Valid qubits WOCB ∧ ¬ ExtensiblyCausal qubits WOCB :=
  ⟨CausalNonpurifiability.appC_OCB_game.1, CausalNonpurifiability.appC_OCB_game.2.2.2.2.2.1⟩

theorem dimension_dichotomy (D : Ports) :
    (∀ W : PMat D, ExtensiblyCausal D W → Purifiable D W) ↔
      min D.m (min D.d (min D.n D.e)) = 1 :=
  CausalNonpurifiability.dimension_dichotomy D

theorem purifiable_causallySeparable (D : Ports) (W : PMat D) (hW : Valid D W)
    (hP : Purifiable D W) : CausallySeparable D W :=
  CausalNonpurifiability.purifiable_causallySeparable D W hW hP

theorem ordered_processes_purifiable (D : Ports) (W : PMat D) (hW : Valid D W)
    (hord : OrderedAB D W ∨ OrderedBA D W) : Purifiable D W :=
  CausalNonpurifiability.ordered_purifiable hW hord

end CausalNonpurifiability.OQP43
