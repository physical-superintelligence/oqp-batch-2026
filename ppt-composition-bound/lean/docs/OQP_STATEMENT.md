# Open Quantum Problems, Problem 38: the entry text

For every `d ≥ 2`, the formalization proves that any `2(d-1)` PPT maps on `d × d` matrices compose
to an entanglement-breaking map. The Problem 38 source text is quoted below;
[FIDELITY.md](FIDELITY.md) maps its wording to the Lean statements.

## Source

- List: Open Quantum Problems, IQOQI Vienna (https://oqp.iqoqi.oeaw.ac.at/).
- Entry: "The PPT-squared conjecture", https://oqp.iqoqi.oeaw.ac.at/the-ppt-squared-conjecture
- Text below: a snapshot of the list taken on 2026-07-31 (CSV export of all entries, SHA-256
  `c7f8cce21170c40d91f9c31068bd8ff5b566fa492c7412d2e34f358c21fe2d83`).
- The text is quoted exactly as stored, including its LaTeX markup (`$$ ... $$`) and its spelling.

## Entry text (verbatim)

> Cite this problem as Problem 38.
>
> ### Problem
>
> Let $$\rho_{AB}$$ and $$\rho_{CD}$$ be quantum states with positive partial transpose (i.e., they are “PPT-states”), and let $$M$$ be a positive operator decribing a yes/no measurement on the BC-system. Then consider the state on AD, conditional on the result of $$M$$ being `yes’, i.e. $$\sigma_{AD}= \lambda tr_{BC}((\rho_{AB}\otimes\rho_{CD})(1_A\otimes M\otimes 1_D))$$ , where $$\lambda$$ is a normalization factor. The conjecture [1] by Matthias Christandl states that all such $$\sigma_{AD}$$ are separable.
>
> Of course, the problem is to prove or disprove this.
>
> ### Background
>
> The process for getting $$\sigma_{AD}$$ is called entanglement swapping, and is a key ingredient of quantum repeaters, which seek to establish secret key over a long distance out of entangled states over smaller distance. While it is possible that PPT states allow the extraction of private key [2], the conjecture would imply that they cannot be used as a resource in a repeater [3].
>
> ### References
>
> [1] List of problems in an open problem session in Banff, conducted by M. B. Ruskai in 2012.
>
> [2] K. Horodecki, M. Horodecki, P. Horodecki, J. Oppenheim: Secure key from bound entanglement, quant-ph/0309110 (2003) and Problem 24.
>
> [3] M. Christandl and R. Ferrara: Private states, quantum data hiding and the swapping of perfect secrecy, arxiv.org/abs/1609.04696
