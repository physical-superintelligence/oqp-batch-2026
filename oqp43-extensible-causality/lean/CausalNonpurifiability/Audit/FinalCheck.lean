module

public import Solution

/-!
# Axiom pin for the theorems of `comparator.json`

`lake build` builds this module. Each `#guard_msgs` below fails the build unless the theorem
depends on exactly the axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

/-- info: 'CausalNonpurifiability.OQP43.not_all_extensiblyCausal_purifiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CausalNonpurifiability.OQP43.not_all_extensiblyCausal_purifiable

/-- info: 'CausalNonpurifiability.OQP43.theorem_1_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CausalNonpurifiability.OQP43.theorem_1_1

/-- info: 'CausalNonpurifiability.OQP43.wq_pauli_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CausalNonpurifiability.OQP43.wq_pauli_form

/-- info: 'CausalNonpurifiability.OQP43.purifiable_iff_transpose_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CausalNonpurifiability.OQP43.purifiable_iff_transpose_formula

/-- info: 'CausalNonpurifiability.OQP43.valid_iff_channels_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CausalNonpurifiability.OQP43.valid_iff_channels_normalized

/-- info: 'CausalNonpurifiability.OQP43.white_process_purifiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CausalNonpurifiability.OQP43.white_process_purifiable

/-- info: 'CausalNonpurifiability.OQP43.swap_table_not_causal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CausalNonpurifiability.OQP43.swap_table_not_causal

/-- info: 'CausalNonpurifiability.OQP43.ocb_process_not_extensiblyCausal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CausalNonpurifiability.OQP43.ocb_process_not_extensiblyCausal

/-- info: 'CausalNonpurifiability.OQP43.dimension_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CausalNonpurifiability.OQP43.dimension_dichotomy

/-- info: 'CausalNonpurifiability.OQP43.purifiable_causallySeparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CausalNonpurifiability.OQP43.purifiable_causallySeparable

/-- info: 'CausalNonpurifiability.OQP43.ordered_processes_purifiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CausalNonpurifiability.OQP43.ordered_processes_purifiable
