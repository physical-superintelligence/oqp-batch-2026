module

public import VacuumBellSeparation.FreeField.MainTheorems
public import VacuumBellSeparation.FreeField.OQP12
public import VacuumBellSeparation.FreeField.LocalAlgebraNonabelian
import VacuumBellSeparation.Audit.FinalCheck

/-!
# VacuumBellSeparation

The library behind `Solution.lean`: the vacuum representation of the massive real free scalar
field in 3+1 dimensions, its local von Neumann algebras, the Summers–Werner Bell correlation, and
the proof that the vacuum Bell correlation of two bounded regions attains the classical bound `1`
once the second region is moved far enough along a fixed spacelike direction
(`FreeField/MainTheorems.lean`), with the plain CHSH form of these results for Open Quantum
Problem 12 (`FreeField/OQP12.lean`) and the noncommutativity of
the local algebras (`FreeField/LocalAlgebraNonabelian.lean`). It imports `Audit/FinalCheck.lean`,
so `lake build` checks that each theorem named in `comparator.json` depends exactly on the axioms
`propext`, `Classical.choice` and `Quot.sound`.
-/
