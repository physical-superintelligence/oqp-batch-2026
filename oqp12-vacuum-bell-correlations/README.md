# The vacuum Bell correlation of the massive free scalar field attains the classical bound for bounded regions beyond a finite separation

## Result

In the vacuum of the massive real free scalar field in 3+1 dimensions, any two fixed bounded regions satisfy the CHSH inequality for all local self-adjoint observables of norm at most one once the second region is translated far enough along a fixed spacelike direction. The vacuum Bell correlation then equals its classical bound, 1. The result addresses [Open Quantum Problem 12](https://oqp.iqoqi.oeaw.ac.at/bell-inequalities-for-long-range-vacuum-correlations), *Bell inequalities for long range vacuum correlations*, for these bounded regions.

The current paper is the letter of 22 October 2026. The formalization follows the full manuscript of 21 October 2026: its Theorem 1.1 and Corollary 1.2 correspond to Theorem 1 and Corollary 1 in the letter. The formalization also contains the CHSH statement with one distance threshold for all spatial directions, existence of the vacuum representation, and noncommutativity of local algebras for nonempty open regions.

## Contents

- Current letter: [PDF](paper/oqp12-vacuum-bell-correlations.pdf) and [LaTeX source](paper/source/).
- Full manuscript: [PDF](paper/full-manuscript/oqp12-vacuum-bell-correlations-full-manuscript.pdf) and [LaTeX source](paper/full-manuscript/source/).
- [Formalization package](lean/), [theorem statements](lean/Challenge.lean), and [proofs](lean/Solution.lean).
- [Manuscript and theorem correspondence](lean/paper/README.md), [paper-to-Lean map](lean/docs/PAPER_TO_LEAN.md), and [definitions and problem correspondence](lean/docs/FIDELITY.md).

## Formalization

The [formalization guide](lean/README.md) gives the pinned toolchain and build commands, run from `lean/`. Main declarations in the included package are:

- `VacuumBellSeparation.OQP12.theorem_1_1`
- `VacuumBellSeparation.OQP12.corollary_1_2`
- `VacuumBellSeparation.OQP12.no_chsh_violation_far_apart`

The [verification receipts](lean/verification/RECEIPTS.md) describe the checks recorded on 21 October 2026 for source commit `6a91bb4b256579eb39f6a5f08f2cb0c1e9bc94e5`.

## Provenance and use of AI

This result was released by Physical Superintelligence (PSI). The mathematics was developed by PSI researchers working with AI models (OpenAI's GPT-6-Astra and GPT-5.6 Pro and Anthropic's Claude Fable 5.1) in automated research workflows at PSI. The Lean formalization was written by AI agents (Anthropic's Claude Opus 5.5 in Claude Code, and OpenAI's GPT-6-Astra in Codex) under PSI's direction. David Turturean is responsible for the correctness of the paper. The paper's AI disclosure has the details; formalization.yaml records which agent did which part.

## Citation

```bibtex
@misc{turturean2026vacuumbell,
  author       = {Turturean, David},
  title        = {The vacuum {Bell} correlation of the massive free scalar field attains the classical bound for bounded regions beyond a finite separation},
  year         = {2026},
  note         = {Preprint, with a Lean 4 formalization},
  howpublished = {\url{https://github.com/physical-superintelligence/oqp-batch-2026/tree/main/oqp12-vacuum-bell-correlations}}
}
```

See the [formalization citation](lean/CITATION.cff) and its reference to the full manuscript.

## License

See the repository [LICENSE](../LICENSE) and [NOTICE](../NOTICE). The formalization includes its own [LICENSE](lean/LICENSE) and [NOTICE](lean/NOTICE).
