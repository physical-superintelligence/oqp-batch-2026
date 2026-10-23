# The optimal CGLMP measurements on maximally entangled states

## Result

For two parties with two measurement settings and `d ≥ 2` outcomes, projective
measurements on the maximally entangled state `Φ_n` have CGLMP value at most the
Fourier-phase value. Equality holds exactly when `n = d k` and the four tracial
measurements are Fourier-phase projectors tensored with the identity on a
`k`-dimensional factor, up to one common unitary. At `n = d`, the maximizing
measurements are rank-one Fourier-phase bases. This is the first assertion of
[Open Quantum Problem 27.B](https://oqp.iqoqi.oeaw.ac.at/the-power-of-cglmp-inequalities/)
in the projective class.

## Contents

- [Paper PDF](paper/oqp27-cglmp-inequalities.pdf), draft of 21 October 2026.
- [Paper source](paper/source/).
- [Lean formalization](lean/).
- [Theorem statements](lean/Challenge.lean) and [proofs](lean/Solution.lean).
- [Paper-to-formalization map](lean/paper/README.md) and
  [problem-to-statement map](lean/docs/FIDELITY.md).
- [Historical verification receipts](lean/verification/RECEIPTS.md).

## Formalization

See the [Lean instructions](lean/README.md) for the pinned environment and build
commands. `OQP27.partB_maximizers_are_fourier_phase` states the bound and equality
case corresponding to Theorems 1 and 3 of the current paper.
`OQP27.fourier_attains_cglmp_value` gives attainment, and
`OQP27.cglmp_witness_tolerance` gives the threshold for the fixed CGLMP witness
under uniform behaviour noise.

The formalization also contains two comparison results at `d = 2^m`:
`OQP27.partB_noise_resistance_not_optimal` gives a smaller critical visibility
for tensor-CHSH measurements when `m ≥ 955`;
`OQP27.partB_kl_discrimination_not_optimal` gives their uniform-input statistical
strength above the Fourier-phase behaviour's strength optimized over input laws
when `m ≥ 41`. The [manuscript map](lean/paper/README.md) identifies the earlier
source labels for these statements.

## Provenance and use of AI

This result was released by Physical Superintelligence (PSI). The mathematics was developed by PSI researchers working with AI models (OpenAI's GPT-6-Astra and Anthropic's Claude Fable 5.1) in automated research workflows at PSI. The Lean formalization was written by AI agents (Anthropic's Claude Opus 5.5 in Claude Code, and OpenAI's GPT-6-Astra in Codex) under PSI's direction. David Turturean and Ning Bao are responsible for the correctness of the paper. The paper's AI disclosure has the details; formalization.yaml records which agent did which part.

## Citation

The [formalization citation](lean/CITATION.cff) records the software and its
bibliographic sources.

## License

See the repository [LICENSE](../LICENSE) and [NOTICE](../NOTICE), and the
standalone formalization's [LICENSE](lean/LICENSE) and [NOTICE](lean/NOTICE).
