# Paper and formalization

The accompanying paper is *An extensibly causal quantum process with no
purification*. In the batch repository, the result directory contains the paper
at `paper/oqp43-extensible-causality.pdf`, its source at
`paper/source/oqp43_letter.tex`, and a picture guide at
`paper/source/process_matrix_pictures.pdf` with its LaTeX source beside it.

## Current paper map

The declarations below are in namespace `CausalNonpurifiability.OQP43`.
[`Challenge.lean`](../Challenge.lean) states the results and
[`Solution.lean`](../Solution.lean) proves them.

| Current paper | Lean declaration |
| --- | --- |
| Negative answer to Open Quantum Problem 43 | `not_all_extensiblyCausal_purifiable` |
| Main theorem: the four-qubit process is valid, has full rank, is extensibly causal and causally nonseparable, and has no purification | `theorem_1_1` |
| Equation defining the process `S` as a rational Pauli sum | `wq_pauli_form`, with the process named `Wq` in Lean |
| Consequence of Theorem A: for positive finite port dimensions, every extensibly causal process is purifiable if and only if the minimum port dimension is one | `dimension_dichotomy` |
| Purifiable bipartite processes are causally separable | `purifiable_causallySeparable` |
| Causally ordered processes are purifiable | `ordered_processes_purifiable` |

The shared process is
`(20 IIII + 10 ZIII + 10 IIZI + 5 ZIZI + 4 IZZI + 4 ZIXZ)/80`,
with tensor factors ordered as `A_I ⊗ A_O ⊗ B_I ⊗ B_O`.

## Source draft

The formalization's bibliographic source is *Extensible causality without
purification* (October 2026). Theorem 1.1, Theorem 6.1, Proposition 9.2 and
appendix references in the formalization identify that source draft.
The table above gives the corresponding statements in the accompanying paper.

[`docs/FIDELITY.md`](../docs/FIDELITY.md) maps the problem text to the definitions,
including the finite dimensions and the purity convention.
[`formalization.yaml`](../formalization.yaml) lists all eleven theorem
declarations and their source relationships.
