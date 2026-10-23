# Paper

The paper of record for this formalization is the PSI manuscript

> *Three-copy nondistillability of qutrit and ququart Werner states*, Physical Superintelligence (PSI),
> manuscript of 21 October 2026.

Paper in preparation.

Theorem 2.1 of the paper at `d = 3`, `α = 1/2` is `ThreeCopyQutritWerner.Endpoints.qutritEndpointInequality`
in [`Challenge.lean`](../Challenge.lean); Theorem 2.1, eqs. (4) and (5), are `sharp_minimum` and
`interior_minimizers`, its statement for unequal local dimensions, in the case `2 ≤ dᵢ ≤ 3`, is
`minimum_formula_unequal_dims`, and Corollary 2.2 is `werner_three_three_copy_iff`,
`werner_three_npt_not_three_copy` and `overlap_le_half` (same namespace). The paper proves Theorem 2.1 and
Corollary 2.2 for `d = 3` and `d = 4`; the formalization covers the qutrit case `d = 3`. The Lean sources cite
theorem, equation and section numbers of the manuscript of 7 October 2026, which the paper of record keeps;
their comments also use that manuscript's letters (for example `C = X B` for `C = X Y†`) and cite its remark on
`d = 2` after Theorem 2.1, which in the paper of record follows from Section 1 and Steps 1 and 5 of the proof
of Corollary 2.2. How the formal statements follow the paper is in [docs/FIDELITY.md](../docs/FIDELITY.md), and
[docs/PAPER_TO_LEAN.md](../docs/PAPER_TO_LEAN.md) maps every numbered statement and equation.
