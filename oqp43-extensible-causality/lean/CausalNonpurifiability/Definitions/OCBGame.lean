module

public import CausalNonpurifiability.Definitions.Causality

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.OCBGame`

The game of Oreshkov, Costa and Brukner [OCB] (manuscript introduction and Appendix C), in the setting/outcome convention of `Prob X Y A B` (`p x y a b` is the
probability of the outcomes `a, b` given the settings `x, y`). The settings are uniformly random
bits: Alice's setting is a bit `x`, Bob's setting is a pair `(y, g)` of bits. If `g = 0`, Bob must
output Alice's bit (`b = x`); if `g = 1`, Alice must output Bob's bit (`a = y`). Dictionary: the
input bits that [OCB] calls `a`, `b` are our settings `x`, `y`; our selector is
`g = 1 - b'`, the complement of the selector in [OCB]. The guesses that [OCB] calls `x`
(Alice's) and `y` (Bob's) are our outcomes `a` and `b`. With this dictionary,
`ocbWin p` is the probability of success.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

/-- Probability of winning the game of [OCB] with uniformly random settings `x`, `y`, `g`: the
average over the eight settings of the probability that `b = x` (when `g = 0`) or `a = y` (when
`g = 1`). -/
noncomputable def ocbWin (p : Prob (Fin 2) (Fin 2 × Fin 2) (Fin 2) (Fin 2)) : ℝ :=
  (1 / 8) * ∑ x : Fin 2, ∑ y : Fin 2,
    ((∑ a : Fin 2, p x (y, 0) a x) + ∑ b : Fin 2, p x (y, 1) y b)

end CausalNonpurifiability
