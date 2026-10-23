# Open Quantum Problems: a PSI batch, October 2026

Five results on [Open Quantum Problems](https://oqp.iqoqi.oeaw.ac.at/).
Each result folder contains a paper and a Lean 4 formalization. Start with a
paper below, or open its result guide for the main theorem statements and
supporting files.

| Problem | Paper | Result guide | Formalization |
| --- | --- | --- | --- |
| [2: Undistillability implies PPT?](https://oqp.iqoqi.oeaw.ac.at/undistillability-implies-ppt) | [Three copies of the Werner state: the sharp curve in dimensions three and four and a bound in every dimension](oqp02-three-copy-werner/paper/oqp02-three-copy-werner.pdf) | [Contents and result](oqp02-three-copy-werner/README.md) | [Lean files](oqp02-three-copy-werner/lean/) |
| [12: Bell inequalities for long-range vacuum correlations](https://oqp.iqoqi.oeaw.ac.at/bell-inequalities-for-long-range-vacuum-correlations) | [The vacuum Bell correlation of the massive free scalar field attains the classical bound for bounded regions beyond a finite separation](oqp12-vacuum-bell-correlations/paper/oqp12-vacuum-bell-correlations.pdf) | [Contents and result](oqp12-vacuum-bell-correlations/README.md) | [Lean files](oqp12-vacuum-bell-correlations/lean/) |
| [27: The power of CGLMP inequalities](https://oqp.iqoqi.oeaw.ac.at/the-power-of-cglmp-inequalities) | [The optimal CGLMP measurements on maximally entangled states](oqp27-cglmp-inequalities/paper/oqp27-cglmp-inequalities.pdf) | [Contents and result](oqp27-cglmp-inequalities/README.md) | [Lean files](oqp27-cglmp-inequalities/lean/) |
| [38: The PPT squared conjecture](https://oqp.iqoqi.oeaw.ac.at/the-ppt-squared-conjecture) | [Entanglement Breaking after 2(d−1) PPT Maps](ppt-composition-bound/paper/ppt-composition-bound.pdf) | [Contents and result](ppt-composition-bound/README.md) | [Lean files](ppt-composition-bound/lean/) |
| [43: Are all extensibly causal processes purifiable?](https://oqp.iqoqi.oeaw.ac.at/are-all-extensibly-causal-processes-purifiable) | [An extensibly causal quantum process with no purification](oqp43-extensible-causality/paper/oqp43-extensible-causality.pdf) | [Contents and result](oqp43-extensible-causality/README.md) | [Lean files](oqp43-extensible-causality/lean/) |

## Layout

```text
<result>/
  README.md     the result, paper, main formal statements and file guide
  paper/        the paper PDF and accompanying manuscript files
  lean/         the formalization, with its own build instructions and citation
```

The formalizations are included as ordinary folders. Each `lean/` folder has
its own pinned dependencies and can be copied out as a standalone project.
The result guides identify the manuscript versions corresponding to the
formal statements.

The three-copy Werner-state result also includes a
[verification package](oqp02-three-copy-werner/verification/README.md).
The vacuum-correlation result includes a
[full manuscript](oqp12-vacuum-bell-correlations/paper/full-manuscript/)
alongside the shorter paper.

## Read and check a formalization

Within each result's `lean/` folder:

- `README.md` gives prerequisites and build commands.
- `Challenge.lean` contains the formal theorem statements.
- `Solution.lean` contains the corresponding proofs.
- `paper/README.md` maps the paper to the formal development.
- `comparator.json` identifies the statements used by the verification command.

Run the commands from the selected `lean/` folder as described in its README.
The commands use the versions in that folder's `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json`.

## Citation and license

Use the selected result's paper citation and its `lean/CITATION.cff` for the
formalization. The root [CITATION.cff](CITATION.cff) describes the collection.

The root [LICENSE](LICENSE) and [NOTICE](NOTICE) state the repository's
default terms. Each result guide links to any additional license and notice
files for its included material.
