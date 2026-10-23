module

public import CausalNonpurifiability.Statement
public import CausalNonpurifiability.Definitions.Process
public import CausalNonpurifiability.Definitions.Instruments
public import CausalNonpurifiability.Definitions.Purity
public import CausalNonpurifiability.Definitions.Hypotheses
public import CausalNonpurifiability.Data.Local
public import CausalNonpurifiability.Data.Qubit
public import CausalNonpurifiability.Certificates.Qubit
public import CausalNonpurifiability.Certificates.Witness
public import CausalNonpurifiability.EC.Bridge
public import CausalNonpurifiability.EC.Rectangles
public import CausalNonpurifiability.Definitions.ExtensibleGeneral

@[expose] public section


/-!
# `CausalNonpurifiability.Main` — public kernel endpoints

Everything here is proved without problem-specific axioms; the conditional statements take
`PurificationNecessity` (Theorem 6.1) as an explicit hypothesis. That hypothesis is itself proved,
`purification_necessity` (`Purification/Necessity.lean`), and the unconditional statements are in
`Unconditional.lean` and `MainTheorem.lean`.

Manuscript anchors: `thm:main` (i) at `m = d = n = e = 2`, `eq:qubit`,
`eq:negative`, §5 (extensible causality), §6.2 (witness).

**Do not describe validity + positivity + witness alone as a solution of
OQP 43**: only `qubit_kernel`, whose `ExtensiblyCausal` clause quantifies over
every finite ancilla and every extended instrument, establishes it.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

/-- **Extensible causality of `W_q`** (§5, Oreshkov–Giarmatzi Def. 3.2): for every finite
ancilla pair `R_A, R_B` (all sizes), every density operator `σ` on `R_A ⊗ R_B`, and every
pair of extended instrument collections, the distribution `bornExtended` is causal.
Proof: `rectangles_qubits` (the rectangle bounds `eq:rectangle` from the signed decomposition,
ordered-event bounds and the dimension-free SOS) fed to `ec_of_rectangles` (transport theorem
`eq:transport` + causal gluing `eq:causal-components`). -/
theorem wq_extensiblyCausal : ExtensiblyCausal qubits Wq :=
  ec_of_rectangles wq_valid rectangles_qubits

/-- Extensible causality of `W_q` in the manuscript's unrestricted form (§2.2, Oreshkov–Giarmatzi
Def. 3.2): arbitrary finite ancilla types, arbitrary finite setting and outcome alphabets
(no nonemptiness assumptions), every density operator and every extended instrument collection. -/
theorem wq_extensiblyCausal_gen : ExtensiblyCausalGen qubits Wq :=
  (extensiblyCausal_iff_gen qubits Wq).mp wq_extensiblyCausal

/-- **Kernel theorem** (`thm:main` (i) on four qubit ports, minus the
purification clause): `W_q` is a valid, positive-definite, extensibly causal
process that is not causally separable. -/
theorem qubit_kernel :
    Valid qubits Wq ∧ Wq.PosDef ∧ ExtensiblyCausal qubits Wq ∧
      ¬ CausallySeparable qubits Wq :=
  ⟨wq_valid, w0_qubit_posDef, wq_extensiblyCausal, wq_not_causallySeparable⟩

/-- Nonpurifiability of `W_q`, conditional on the published purification
necessity theorem (`eq:purcs`, passed as a parameter). -/
theorem qubit_not_purifiable_of_purCS (hPurCS : PurificationNecessity) :
    ¬ Purifiable qubits Wq :=
  fun hPur => qubit_kernel.2.2.2 (hPurCS qubits Wq qubit_kernel.1 hPur)

/-- **Negative answer to OQP 43** on four qubit ports, conditional on
`PurificationNecessity`: an extensibly causal process with no finite
purification exists. -/
theorem oqp43_negative_of_purCS (hPurCS : PurificationNecessity) :
    ∃ W : PMat qubits, ExtensiblyCausal qubits W ∧ ¬ Purifiable qubits W :=
  ⟨Wq, qubit_kernel.2.2.1, qubit_not_purifiable_of_purCS hPurCS⟩

end CausalNonpurifiability
