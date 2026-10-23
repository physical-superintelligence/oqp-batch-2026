module

public import Solution

/-!
# Axiom check

Building this module checks that each theorem listed in `comparator.json` depends on exactly the
axioms `propext`, `Classical.choice` and `Quot.sound`: each `#guard_msgs` below fails the build if
the output of `#print axioms` differs from the expected line.
-/

/-- info: 'ThreeCopyQutritWerner.Endpoints.qutritEndpointInequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.qutritEndpointInequality

/-- info: 'ThreeCopyQutritWerner.Endpoints.sharp_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.sharp_minimum

/-- info: 'ThreeCopyQutritWerner.Endpoints.interior_minimizers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.interior_minimizers

/-- info: 'ThreeCopyQutritWerner.Endpoints.minimum_formula_unequal_dims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.minimum_formula_unequal_dims

/-- info: 'ThreeCopyQutritWerner.Endpoints.werner_three_three_copy_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.werner_three_three_copy_iff

/-- info: 'ThreeCopyQutritWerner.Endpoints.werner_three_npt_not_three_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.werner_three_npt_not_three_copy

/-- info: 'ThreeCopyQutritWerner.Endpoints.overlap_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.overlap_le_half

/-- info: 'ThreeCopyQutritWerner.Endpoints.continuation_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.continuation_identity

/-- info: 'ThreeCopyQutritWerner.Endpoints.formR_nonneg_rank_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.formR_nonneg_rank_two

/-- info: 'ThreeCopyQutritWerner.Endpoints.cutForms_nonneg_rank_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.cutForms_nonneg_rank_two

/-- info: 'ThreeCopyQutritWerner.Endpoints.three_copy_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.three_copy_expectation

/-- info: 'ThreeCopyQutritWerner.Endpoints.schmidtRank_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.schmidtRank_vec

/-- info: 'ThreeCopyQutritWerner.Endpoints.werner_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.werner_state

/-- info: 'ThreeCopyQutritWerner.Endpoints.werner_npt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.werner_npt_iff

/-- info: 'ThreeCopyQutritWerner.Endpoints.werner_three_one_copy_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.werner_three_one_copy_iff

/-- info: 'ThreeCopyQutritWerner.Endpoints.werner_three_three_copy_of_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.werner_three_three_copy_of_gt

/-- info: 'ThreeCopyQutritWerner.Endpoints.werner_three_not_three_copy_of_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.werner_three_not_three_copy_of_nonpos

/-- info: 'ThreeCopyQutritWerner.Endpoints.werner_three_not_three_copy_of_le_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.werner_three_not_three_copy_of_le_third

/-- info: 'ThreeCopyQutritWerner.Endpoints.interior_shape_attains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.interior_shape_attains

/-- info: 'ThreeCopyQutritWerner.Endpoints.familyI_endpoint_zero_any_plane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.familyI_endpoint_zero_any_plane

/-- info: 'ThreeCopyQutritWerner.Endpoints.endpoint_zero_rank_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.endpoint_zero_rank_two

/-- info: 'ThreeCopyQutritWerner.Endpoints.overlap_le_half_of_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.overlap_le_half_of_nonpos

/-- info: 'ThreeCopyQutritWerner.Endpoints.overlap_le_half_of_le_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.overlap_le_half_of_le_third

/-- info: 'ThreeCopyQutritWerner.Endpoints.filter_iff_rank_two_detectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.filter_iff_rank_two_detectable

/-- info: 'ThreeCopyQutritWerner.Endpoints.sharp_curve_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.sharp_curve_attained

/-- info: 'ThreeCopyQutritWerner.Endpoints.sharp_minimum_of_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.sharp_minimum_of_endpoint

/-- info: 'ThreeCopyQutritWerner.Endpoints.minimum_formula_of_card_of_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.minimum_formula_of_card_of_endpoint

/-- info: 'ThreeCopyQutritWerner.Endpoints.interior_minimizers_of_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.interior_minimizers_of_endpoint

/-- info: 'ThreeCopyQutritWerner.Endpoints.werner_three_three_copy_iff_of_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.werner_three_three_copy_iff_of_endpoint

/-- info: 'ThreeCopyQutritWerner.Endpoints.werner_three_npt_not_three_copy_of_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.werner_three_npt_not_three_copy_of_endpoint

/-- info: 'ThreeCopyQutritWerner.Endpoints.overlap_le_half_of_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.overlap_le_half_of_endpoint

/-- info: 'ThreeCopyQutritWerner.Endpoints.formR_eq_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.formR_eq_proj

/-- info: 'ThreeCopyQutritWerner.Endpoints.rank_raise_ptrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.rank_raise_ptrace

/-- info: 'ThreeCopyQutritWerner.Endpoints.three_copy_ppt_of_le_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.three_copy_ppt_of_le_third

/-- info: 'ThreeCopyQutritWerner.Endpoints.werner_two_half_separable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.werner_two_half_separable

/-- info: 'ThreeCopyQutritWerner.Endpoints.noisy_family_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.noisy_family_posDef

/-- info: 'ThreeCopyQutritWerner.Endpoints.noisy_family_npt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.noisy_family_npt

/-- info: 'ThreeCopyQutritWerner.Endpoints.sharp_minimum_isLeast_of_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.sharp_minimum_isLeast_of_endpoint

/-- info: 'ThreeCopyQutritWerner.Endpoints.zero_families_are_half_singular_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.zero_families_are_half_singular_zeros

/-- info: 'ThreeCopyQutritWerner.Endpoints.qutrit_endpoint_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.qutrit_endpoint_of_certificate

/-- info: 'ThreeCopyQutritWerner.Endpoints.noisy_family_three_copy_of_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.noisy_family_three_copy_of_endpoint

/-- info: 'ThreeCopyQutritWerner.Endpoints.projector_cut_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.projector_cut_identity

/-- info: 'ThreeCopyQutritWerner.Endpoints.cutForm_two_plane_projector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.cutForm_two_plane_projector

/-- info: 'ThreeCopyQutritWerner.Endpoints.two_plane_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.two_plane_product

/-- info: 'ThreeCopyQutritWerner.Endpoints.twoQubit_separable_iff_ppt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.twoQubit_separable_iff_ppt

/-- info: 'ThreeCopyQutritWerner.Endpoints.appendixC_input1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.appendixC_input1

/-- info: 'ThreeCopyQutritWerner.Endpoints.appendixC_input2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.appendixC_input2

/-- info: 'ThreeCopyQutritWerner.Endpoints.appendixC_input3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeCopyQutritWerner.Endpoints.appendixC_input3
