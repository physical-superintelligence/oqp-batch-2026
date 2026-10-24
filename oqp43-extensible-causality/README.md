# An extensibly causal quantum process with no purification

## Result

An explicit four-qubit process is extensibly causal and not purifiable, answering
[Open Quantum Problem 43](https://oqp.iqoqi.oeaw.ac.at/are-all-extensibly-causal-processes-purifiable)
in the negative. The paper calls the process `S`; the formalization calls the same
Pauli expression `Wq`.

## Contents

| Material | Location |
| --- | --- |
| Current paper | [PDF](paper/oqp43-extensible-causality.pdf) |
| Paper source | [LaTeX and bibliography](paper/source/), starting with [`oqp43_letter.tex`](paper/source/oqp43_letter.tex) |
| Picture guide | [PDF](paper/source/process_matrix_pictures.pdf) and [LaTeX source](paper/source/process_matrix_pictures.tex) |
| Formalization and build instructions | [`lean/`](lean/README.md) |
| Theorem statements | [`lean/Challenge.lean`](lean/Challenge.lean) |
| Proofs | [`lean/Solution.lean`](lean/Solution.lean) |
| Paper-to-formalization map | [`lean/paper/README.md`](lean/paper/README.md) |
| Problem definitions and theorem map | [`lean/docs/FIDELITY.md`](lean/docs/FIDELITY.md) |

## Formalization

The Lean development proves the explicit counterexample, its Pauli expression,
and the dimension dichotomy: for two parties with positive finite port
dimensions `(m, d, n, e)`, every extensibly causal process is purifiable exactly
when the minimum port dimension is one.

The declarations in namespace `CausalNonpurifiability.OQP43` include
`not_all_extensiblyCausal_purifiable`, `theorem_1_1`, `wq_pauli_form`, and
`dimension_dichotomy`. The [paper map](lean/paper/README.md) connects those
declarations to the current paper and identifies the source draft used for the
formalization's theorem numbering.

Use the pinned commands in [`lean/README.md`](lean/README.md).
The [verification receipts](lean/verification/RECEIPTS.md) record the checks of
commit `3e78c71a3666e793b8bc1efb19113873c652a9a1` on 14 October 2026.

## Provenance and use of AI

This result was released by Physical Superintelligence (PSI). The mathematics was developed by PSI researchers working with AI models (OpenAI's GPT-6-Astra and Anthropic's Claude Fable 5.1, Claude Opus 5 and Claude Opus 5.5) in automated research workflows at PSI. The Lean formalization was written by AI agents (Anthropic's Claude Fable 5.1 and Claude Opus 5.5 in Claude Code, and OpenAI's GPT-6-Astra in Codex) under PSI's direction. David Turturean and Ning Bao are responsible for the correctness of the paper. The paper's AI disclosure has the details; formalization.yaml records which agent did which part.

## Citation

Cite the paper as follows:

> David Turturean and Ning Bao (2026). *An extensibly causal quantum process with no purification*. Preprint.

[PDF at the cited version](https://github.com/physical-superintelligence/oqp-batch-2026/blob/7049357c42a8fe85262da08fdc10d57b4d9e67a0/oqp43-extensible-causality/paper/oqp43-extensible-causality.pdf).

```bibtex
@unpublished{turturean2026extensible,
  author = {Turturean, David and Bao, Ning},
  title = {{An extensibly causal quantum process with no purification}},
  year = {2026},
  note = {Preprint; repository snapshot of 23 October 2026.},
  url = {https://github.com/physical-superintelligence/oqp-batch-2026/blob/7049357c42a8fe85262da08fdc10d57b4d9e67a0/oqp43-extensible-causality/paper/oqp43-extensible-causality.pdf}
}
```

The [combined BibTeX file](../CITATIONS.bib) contains these paper citations. If you use the Lean formalization, also cite its [software record](lean/CITATION.cff) and identify the commit used. Earlier source drafts remain identified in the formalization metadata for theorem correspondence.

## License

See the batch [LICENSE](../LICENSE) and [NOTICE](../NOTICE), and the
formalization's [LICENSE](lean/LICENSE) and [NOTICE](lean/NOTICE).
