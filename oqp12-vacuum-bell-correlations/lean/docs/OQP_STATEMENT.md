# Open Quantum Problem 12: the statement

**Source.** IQOQI Vienna, Open Quantum Problems, Problem 12, "Bell inequalities for long range vacuum
correlations", <https://oqp.iqoqi.oeaw.ac.at/bell-inequalities-for-long-range-vacuum-correlations>.
Archived copy (Internet Archive, 29 October 2023):
<https://web.archive.org/web/20231029013530/https://oqp.iqoqi.oeaw.ac.at/bell-inequalities-for-long-range-vacuum-correlations>.

**Text.** The two paragraphs below are the problem as published on the page, checked word for word
against the Internet Archive copy of 29 October 2023 on 21 October 2026, when the live page returned a
server error. The paper of record (see `paper/README.md`) quotes the same text and cites the page and
that archive copy.

## Verbatim text

> It is well known [1] that vacuum fluctuations maximally violate the CHSH-Bell inequalities for suitable
> spacelike separated observables, and that this violation goes to zero as the two localization regions are
> moved apart.
>
> Decide whether some (necessarily small) violation of the inequalities is possible for regions arbitrarily
> far apart. For definiteness, consider a massive scalar free relativistic Bose field.

Reference [1] of the problem is S. J. Summers and R. F. Werner, "The vacuum violates Bell's inequalities",
Physics Letters A 110 (1985) 257–259.

## What is answered here

For two **bounded** regions of 3+1-dimensional Minkowski space and the real massive free scalar field, the
answer is **no** when the second region is moved far enough along a fixed spacelike direction, or by a
spatial translation of length at least a threshold that is the same for all directions (the thresholds
depend on the mass and the regions, and the one along a fixed direction also on that direction): then every choice of local observables satisfies the CHSH inequality in the
vacuum. `Challenge.lean` states this as `VacuumBellSeparation.OQP12.no_chsh_violation_far_apart`
(separation along any fixed spacelike direction) and `VacuumBellSeparation.OQP12.no_chsh_violation_far_apart_uniform`
(spatial separation in any direction, with one threshold for all directions). `docs/FIDELITY.md` maps each
phrase of the text above to the Lean statements.
