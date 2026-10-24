# Entanglement Breaking after 2(d-1) PPT Maps

## Result

For every `d ≥ 2`, any `2(d-1)` PPT maps on `d × d` complex matrices compose to an entanglement-breaking map. The maps may differ. A PPT map is completely positive and completely copositive; trace preservation is optional. Consequently, the entanglement-breaking index of every PPT map is at most `2(d-1)`.

Open Quantum Problem [38, *The PPT-squared conjecture*](https://oqp.iqoqi.oeaw.ac.at/the-ppt-squared-conjecture) concerns compositions of two PPT maps.

## Contents

- [Paper PDF](paper/ppt-composition-bound.pdf), by David Turturean and Ning Bao.
- [Paper source](paper/source/), with entry point `ppt_composition_prl_draft.tex`.
- [Lean formalization](lean/).
- [Theorem statements](lean/Challenge.lean) and [proofs](lean/Solution.lean).
- [Paper-to-formalization map](lean/docs/FIDELITY.md).
- [Historical verification receipts](lean/verification/RECEIPTS.md), with the dates and file hashes of the recorded checks.

## Formalization

The [standalone instructions](lean/README.md) give the pinned toolchain and build commands. Theorem 1 is represented by `PPTCompositionBound.compose_ppt_maps_entanglementBreaking` and `PPTCompositionBound.ebIndex_le_of_isPPTMap`. The development also includes `PPTCompositionBound.compose_at_least_ppt_maps_entanglementBreaking` for compositions of any `N ≥ 2(d-1)` PPT maps.

## Provenance and use of AI

This result was released by Physical Superintelligence (PSI). The mathematics was developed by PSI researchers working with AI models (OpenAI's GPT-5.6-Sol, GPT-5.6 Pro and GPT-6-Astra and Anthropic's Claude Opus 5) in automated research workflows at PSI. The Lean formalization was written by AI agents (Anthropic's Claude Opus 5.5 in Claude Code, and OpenAI's GPT-6-Astra in Codex) under PSI's direction. David Turturean and Ning Bao are responsible for the correctness of the paper. The paper's AI disclosure has the details; formalization.yaml records which agent did which part.

## Citation

Cite the paper as follows:

> David Turturean and Ning Bao (2026). *Entanglement Breaking after 2(d-1) PPT Maps*. Preprint.

[PDF at the cited version](https://github.com/physical-superintelligence/oqp-batch-2026/blob/7049357c42a8fe85262da08fdc10d57b4d9e67a0/ppt-composition-bound/paper/ppt-composition-bound.pdf).

```bibtex
@unpublished{turturean2026ppt,
  author = {Turturean, David and Bao, Ning},
  title = {{Entanglement Breaking after 2(d-1) PPT Maps}},
  year = {2026},
  note = {Preprint; repository snapshot of 23 October 2026.},
  url = {https://github.com/physical-superintelligence/oqp-batch-2026/blob/7049357c42a8fe85262da08fdc10d57b4d9e67a0/ppt-composition-bound/paper/ppt-composition-bound.pdf}
}
```

The [combined BibTeX file](../CITATIONS.bib) contains these paper citations. If you use the Lean formalization, also cite its [software record](lean/CITATION.cff) and identify the commit used.

## License

See the repository [LICENSE](../LICENSE) and [NOTICE](../NOTICE), and the formalization's [LICENSE](lean/LICENSE) and [NOTICE](lean/NOTICE).
