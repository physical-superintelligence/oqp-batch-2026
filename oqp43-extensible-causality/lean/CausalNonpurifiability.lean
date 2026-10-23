module

public import CausalNonpurifiability.MainTheorem
public import CausalNonpurifiability.Boundary.Transpose
public import CausalNonpurifiability.Propositions
public import CausalNonpurifiability.OCBGame

/-!
# `CausalNonpurifiability`

Root of the library: the import cone of the theorems proved in `Solution.lean`.

* `MainTheorem`: Theorem 1.1 (`theorem_intro`), the Pauli form of `W_q` (`eq_qubit_pauli`), and,
  through `Unconditional`, the answer `oqp43_negative` and the dichotomy `dimension_dichotomy`;
  `Purification/Necessity.lean` proves that purifiable processes are causally separable.
* `Boundary/Transpose`: the problem's transposed recovery formula
  (`purifiable_iff_transpose_convention`).
* `Propositions`: the purifiable maximally mixed process (`white_process`) and a non-causal table
  (`not_causal_swap`).
* `OCBGame`: the process of Oreshkov, Costa and Brukner is not extensibly causal
  (`appC_OCB_game`).
-/
