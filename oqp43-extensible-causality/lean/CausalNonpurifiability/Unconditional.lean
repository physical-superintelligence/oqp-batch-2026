module

public import CausalNonpurifiability.Purification.Necessity
public import CausalNonpurifiability.Main
public import CausalNonpurifiability.Full
public import CausalNonpurifiability.Dichotomy

@[expose] public section


/-!
# `CausalNonpurifiability.Unconditional`

The "not purifiable" clauses of Theorems 1.1 and 3.1 and the dichotomy `eq:dichotomy`, without
the hypothesis `PurificationNecessity`: each statement instantiates the corresponding
`*_of_purCS` statement with `purification_necessity` (Theorem 6.1,
`Purification/Necessity.lean`).

* `qubit_not_purifiable`, `oqp43_negative` — four qubits (Theorem 1.1, Corollary 7.2).
* `uniform_not_purifiable`, `dichotomy_forward` — all local dimensions `≥ 2` (Theorem 3.1(i)).
* `ball_not_purifiable`, `ball_not_purifiable_norm` — the ball `eq:ball` (Theorem 3.1(ii)).
* `dimension_dichotomy` — `eq:dichotomy`.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

/-- `W_q` is not purifiable (Theorem 1.1; Corollary 7.2 for four qubits). -/
theorem qubit_not_purifiable : ¬ Purifiable qubits Wq :=
  qubit_not_purifiable_of_purCS purification_necessity

/-- **Negative answer to Problem 43**: an extensibly causal process on four qubits that is not
purifiable. -/
theorem oqp43_negative :
    ∃ W : PMat qubits, ExtensiblyCausal qubits W ∧ ¬ Purifiable qubits W :=
  oqp43_negative_of_purCS purification_necessity

/-- `W_0` is not purifiable when all local dimensions are at least `2` (Theorem 3.1(i),
Corollary 7.2). -/
theorem uniform_not_purifiable (D : Ports) (hD : AllPortsGE2 D) :
    ¬ Purifiable D (toC (W0 D.m D.d D.n D.e)) :=
  uniform_not_purifiable_of_purCS D purification_necessity hD

/-- For all local dimensions at least `2` there is an extensibly causal process that is not
purifiable. -/
theorem dichotomy_forward (D : Ports) (hD : AllPortsGE2 D) :
    ∃ W : PMat D, ExtensiblyCausal D W ∧ ¬ Purifiable D W :=
  dichotomy_forward_of_purCS D purification_necessity hD

/-- No point of the ball `eq:ball` is purifiable (Theorem 3.1(ii)), positive-bound form. -/
theorem ball_not_purifiable (D : Ports) (hD : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    ¬ Purifiable D (WcC D + H) :=
  ball_not_purifiable_of_purCS D purification_necessity hD hH

/-- No point of the ball `eq:ball` is purifiable (Theorem 3.1(ii)), operator-norm form. -/
theorem ball_not_purifiable_norm (D : Ports) (hD : AllPortsGE2 D) {H : PMat D} (hLV : InLV D H)
    (htr : H.trace = 0) (hnorm : opNorm H ≤ 1 / (300 * D.m * D.n)) :
    ¬ Purifiable D (WcC D + H) :=
  ball_not_purifiable_of_purCS_norm D purification_necessity hD hLV htr hnorm

/-- **`eq:dichotomy`**: every extensibly causal process on `A_I A_O B_I B_O` is purifiable if and
only if one of the local dimensions is `1`. -/
theorem dimension_dichotomy (D : Ports) :
    (∀ W : PMat D, ExtensiblyCausal D W → Purifiable D W) ↔
      min D.m (min D.d (min D.n D.e)) = 1 :=
  dimension_dichotomy_of_purCS purification_necessity D

end CausalNonpurifiability
