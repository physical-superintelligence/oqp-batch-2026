module

public import Solution

/-!
# Axiom check

Building this module checks that each theorem listed in `comparator.json` depends on exactly the
axioms `propext`, `Classical.choice` and `Quot.sound`: each `#guard_msgs` below fails the build if
the output of `#print axioms` differs from the expected line.
-/

/-- info: 'PPTCompositionBound.compose_ppt_maps_entanglementBreaking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.compose_ppt_maps_entanglementBreaking

/-- info: 'PPTCompositionBound.ebIndex_le_of_isPPTMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.ebIndex_le_of_isPPTMap

/-- info: 'PPTCompositionBound.compose_at_least_ppt_maps_entanglementBreaking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.compose_at_least_ppt_maps_entanglementBreaking

/-- info: 'PPTCompositionBound.compose_ppt_map_interleaved_entanglementBreaking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.compose_ppt_map_interleaved_entanglementBreaking

/-- info: 'PPTCompositionBound.exists_posSemidef_not_isSeparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.exists_posSemidef_not_isSeparable

/-- info: 'PPTCompositionBound.id_not_entanglementBreaking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.id_not_entanglementBreaking

/-- info: 'PPTCompositionBound.choi_isCompletelyPositive_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.choi_isCompletelyPositive_iff

/-- info: 'PPTCompositionBound.choi_isPPTMap_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.choi_isPPTMap_iff

/-- info: 'PPTCompositionBound.choi_isEntanglementBreaking_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.choi_isEntanglementBreaking_iff

/-- info: 'PPTCompositionBound.transposeMap_isCompletelyCopositive_not_isCompletelyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.transposeMap_isCompletelyCopositive_not_isCompletelyPositive

/-- info: 'PPTCompositionBound.compList_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.compList_pair

/-- info: 'PPTCompositionBound.zero_map_isPPTMap_and_ebIndex_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.zero_map_isPPTMap_and_ebIndex_eq_one

/-- info: 'PPTCompositionBound.ebIndex_id_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PPTCompositionBound.ebIndex_id_eq_top
