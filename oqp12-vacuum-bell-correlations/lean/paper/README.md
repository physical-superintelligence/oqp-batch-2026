# Paper

The source for this formalization is the full manuscript

> *The vacuum Bell correlation of the massive free scalar field attains the classical bound for bounded regions beyond a finite separation*, Physical Superintelligence (PSI),
> version of 21 October 2026.

The theorem and equation numbers in this package refer to that full manuscript.
The letter of 22 October 2026 has the same title and presents Theorem 1.1 and
Corollary 1.2 as Theorem 1 and Corollary 1. Both editions are included in the batch
repository's result directory, under `paper/` and `paper/full-manuscript/`.

Theorem 1.1 of the paper is `VacuumBellSeparation.OQP12.theorem_1_1` and Corollary 1.2 is
`VacuumBellSeparation.OQP12.corollary_1_2` in [`Challenge.lean`](../Challenge.lean). The headline
`VacuumBellSeparation.OQP12.no_chsh_violation_far_apart` restates Corollary 1.2 as the CHSH inequality for
all local observables, the form in which Open Quantum Problem 12 asks the question. How the formal
statements follow the paper and the problem is in [docs/FIDELITY.md](../docs/FIDELITY.md); [docs/PAPER_TO_LEAN.md](../docs/PAPER_TO_LEAN.md)
maps the paper's numbered statements and equations to the Lean library.
