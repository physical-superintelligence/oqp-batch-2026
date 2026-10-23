module

public import CausalNonpurifiability.Definitions.ConvexFormCore
public import CausalNonpurifiability.Definitions.Process

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.ConvexForm`

Definition 2.4 of the manuscript (`def:order`) in its own words: a process is causally separable
if it is a convex combination of a process of order `A ≺ B` and a process of order `B ≺ A`.
The library works with the sum form `CausallySeparable` (`Definitions/Process.lean`); the two
agree for processes by `causallySeparable_iff_convex` (`Definitions/Separability.lean`).
-/

set_option autoImplicit false

namespace CausalNonpurifiability

end CausalNonpurifiability
