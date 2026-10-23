module

public import PPTCompositionBound.Main
public import PPTCompositionBound.AtLeast
public import PPTCompositionBound.ChoiBridge
public import PPTCompositionBound.NonTrivial
public import PPTCompositionBound.Counterexample

/-!
# PPTCompositionBound

Root of the library: the import cone of the theorems advertised in `Challenge.lean`.

* `PPTCompositionBound.Defs`: PPT maps, separability, entanglement-breaking maps, ordered
  compositions and the entanglement-breaking index.
* `PPTCompositionBound.Main`: any `2 j` PPT maps on `M_n` with `|n| ≤ j + 1` compose to an
  entanglement-breaking map, and the index bound (Theorem 1 of the paper).
* `PPTCompositionBound.AtLeast`: the same for compositions of at least `2 j` PPT maps.
* `PPTCompositionBound.ChoiBridge`: Choi-matrix characterizations of complete positivity, PPT maps
  and entanglement-breaking maps.
* `PPTCompositionBound.NonTrivial`: the definitions are not vacuous (an entangled positive operator;
  the identity map is not entanglement breaking).
* `PPTCompositionBound.Counterexample`: transposition is completely copositive but not completely
  positive, so a PPT map must be required to be both.
-/
