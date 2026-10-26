# Three copies of the Werner state: the sharp curve in dimensions three and four and a bound in every dimension

## Result

For local dimensions 3 and 4 and 0 ≤ α ≤ 1/2, the minimum of the three-copy form q_α on unit matrices of rank at most two is exactly (1 − 2α)(1 − α)², so three copies of the Werner state ρ_α are distillable exactly when α > 1/2; and in every finite local dimension three copies are not distillable for α ≤ 37/80 = 0.4625, so NPT Werner states that survive three copies exist for every d ≥ 3.

**Open Quantum Problem:** [2](https://oqp.iqoqi.oeaw.ac.at/undistillability-implies-ppt), *Undistillability implies PPT?* (the question behind the result).

## Contents

[*Three copies of the Werner state: the sharp curve in dimensions three and four and a bound in every dimension*](paper/oqp02-three-copy-werner.pdf), Ian MacCormack (Physical Superintelligence PBC) and Ning Bao (Northeastern University; Brookhaven National Laboratory), 23 October 2026. Its LaTeX source is in [`paper/source/`](paper/source).

- [Paper source guide](paper/source/README.md), with `main.tex` as the entry point and the existing build script.
- [Lean formalization](lean/), [theorem statements](lean/Challenge.lean) and [proofs](lean/Solution.lean).
- [Paper-to-Lean map](lean/docs/PAPER_TO_LEAN.md) and [statement guide](lean/docs/FIDELITY.md) for the formalized manuscript.
- [Verification package](verification/README.md), with certificate data, programs and run receipts for the current paper.
- [Earlier draft](drafts/2026-09-21/), files archived on 21 September 2026, with their timestamps and a verification command.

[`verification/`](verification) backs the paper's two computer-verified statements: pinned, digest-checked scripts that fetch and replay the published d = 3 and d = 4 endpoint certificates (Theorem 6.4), and the dimension-uniform certificate of Theorem 7.2 with its exact verifier; with control scripts, the zero census of Remark 4.5, run receipts and `SHA256SUMS`. Its [`README.md`](verification/README.md) gives the commands, the expected outputs and the interface between the paper and every stored object.

## Formalization

The [formalization guide](lean/README.md) gives build instructions for the pinned Lean and Mathlib versions. The included Lean development formalizes the qutrit case (d = 3) of Theorems 1.1 and 1.2: the endpoint inequality from an exact certificate, the sharp curve, its minimisers and the distillability threshold. It also includes Proposition 4.2(a), the three families of endpoint zeros, and Corollary 5.3 for k = 3, full-rank NPT states that survive three copies.

The formalization was written against the 21 October 2026 manuscript *Three-copy nondistillability of qutrit and ququart Werner states*. Its [paper record](lean/paper/README.md), [paper-to-Lean map](lean/docs/PAPER_TO_LEAN.md) and [metadata](lean/formalization.yaml) retain that manuscript's numbering: Theorem 2.1 and Corollary 2.2 at d = 3 correspond to Theorems 1.1 and 1.2 of the current paper. [Historical verification receipts](lean/verification/RECEIPTS.md) identify the checked formalization commit `787448536a506e69c3f15d953257f224f095c5eb`.

The 48 statements in [Challenge.lean](lean/Challenge.lean) have proofs in [Solution.lean](lean/Solution.lean). Main declarations include:

- `ThreeCopyQutritWerner.Endpoints.qutritEndpointInequality`
- `ThreeCopyQutritWerner.Endpoints.sharp_minimum`
- `ThreeCopyQutritWerner.Endpoints.werner_three_three_copy_iff`
- `ThreeCopyQutritWerner.Endpoints.werner_three_npt_not_three_copy`

## Provenance and use of AI

This result was released by Physical Superintelligence (PSI). The mathematics was developed by PSI researchers working with AI models (Anthropic's Claude Fable 5.1 and Claude Opus 4.8, and OpenAI's GPT-5.6 and GPT-6-Astra) in automated research workflows at PSI. The Lean formalization was written by AI agents (OpenAI's GPT-6-Astra in Codex) under PSI's direction. Ian MacCormack and Ning Bao are responsible for the correctness of the paper. The paper's AI disclosure has the details; formalization.yaml records which agent did which part.

## Citation

Cite the paper as follows:

> Ian MacCormack and Ning Bao (2026). *Three copies of the Werner state: the sharp curve in dimensions three and four and a bound in every dimension*. Preprint.

[PDF at the cited version](https://github.com/physical-superintelligence/oqp-batch-2026/blob/7049357c42a8fe85262da08fdc10d57b4d9e67a0/oqp02-three-copy-werner/paper/oqp02-three-copy-werner.pdf).

```bibtex
@unpublished{maccormack2026werner,
  author = {MacCormack, Ian and Bao, Ning},
  title = {{Three copies of the Werner state: the sharp curve in dimensions three and four and a bound in every dimension}},
  year = {2026},
  note = {Preprint; repository snapshot of 23 October 2026.},
  url = {https://github.com/physical-superintelligence/oqp-batch-2026/blob/7049357c42a8fe85262da08fdc10d57b4d9e67a0/oqp02-three-copy-werner/paper/oqp02-three-copy-werner.pdf}
}
```

The [combined BibTeX file](../CITATIONS.bib) contains these paper citations. If you use the Lean formalization, also cite its [software record](lean/CITATION.cff) and identify the commit used. Earlier source drafts remain identified in the formalization metadata for theorem correspondence.

## License

The paper is copyright Physical Superintelligence PBC. The verification package's code is released under the MIT
licence and its data, logs and documentation under CC BY 4.0 ([`LICENSE.md`](LICENSE.md)); `lean/` under the Apache
License 2.0 ([`lean/LICENSE`](lean/LICENSE)). Third-party material is listed in [`NOTICE`](NOTICE).
