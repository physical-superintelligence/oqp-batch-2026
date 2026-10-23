module

public import Solution

/-!
# Axiom pin for the theorems of `comparator.json`

`lake build` builds this module. Each `#guard_msgs` below fails the build unless the theorem
depends on exactly the axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

/-- info: 'OQP27.partB_maximizers_are_fourier_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.partB_maximizers_are_fourier_phase

/-- info: 'OQP27.partB_noise_resistance_not_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.partB_noise_resistance_not_optimal

/-- info: 'OQP27.partB_kl_discrimination_not_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.partB_kl_discrimination_not_optimal

/-- info: 'OQP27.cglmp_local_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.cglmp_local_bound

/-- info: 'OQP27.fourier_attains_cglmp_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.fourier_attains_cglmp_value

/-- info: 'OQP27.fourier_projectors_pvm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.fourier_projectors_pvm

/-- info: 'OQP27.tracial_table_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.tracial_table_physical

/-- info: 'OQP27.tensor_chsh_rank_one_pvm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.tensor_chsh_rank_one_pvm

/-- info: 'OQP27.cglmp_witness_tolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.cglmp_witness_tolerance

/-- info: 'OQP27.noise_separation_955' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.noise_separation_955

/-- info: 'OQP27.statistical_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.statistical_separation

/-- info: 'OQP27.bgp_facet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.bgp_facet

/-- info: 'OQP27.bgp_relative_interior_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.bgp_relative_interior_point

/-- info: 'OQP27.bgp_no_signalling_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.bgp_no_signalling_violation

/-- info: 'OQP27.bgp_not_cglmp_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.bgp_not_cglmp_four

/-- info: 'OQP27.bgp_no_fusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OQP27.bgp_no_fusion
