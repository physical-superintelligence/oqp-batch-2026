module

import Solution

/-!
# Axiom check of the theorems named in `comparator.json`

The library root `VacuumBellSeparation.lean` imports this module, so `lake build` runs it. For each
theorem of `Solution.lean` named in `comparator.json`, `#guard_msgs` fails the build unless
`#print axioms` reports exactly the axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

/-- info: 'VacuumBellSeparation.OQP12.no_chsh_violation_far_apart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VacuumBellSeparation.OQP12.no_chsh_violation_far_apart

/-- info: 'VacuumBellSeparation.OQP12.theorem_1_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VacuumBellSeparation.OQP12.theorem_1_1

/-- info: 'VacuumBellSeparation.OQP12.corollary_1_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VacuumBellSeparation.OQP12.corollary_1_2

/-- info: 'VacuumBellSeparation.OQP12.freeFieldVacuum_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VacuumBellSeparation.OQP12.freeFieldVacuum_exists

/-- info: 'VacuumBellSeparation.OQP12.no_chsh_violation_far_apart_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VacuumBellSeparation.OQP12.no_chsh_violation_far_apart_uniform

/-- info: 'VacuumBellSeparation.OQP12.localAlgebra_open_nonabelian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VacuumBellSeparation.OQP12.localAlgebra_open_nonabelian
