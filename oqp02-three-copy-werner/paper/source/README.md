# Paper source

`main.tex` + `refs.bib` → `main.pdf` (REVTeX 4.2, `pra`, two columns, 14 pages); [`../oqp02-three-copy-werner.pdf`](../oqp02-three-copy-werner.pdf)
is that file. Build with `./build.sh` (or `pdflatex main; bibtex main; pdflatex main; pdflatex main`). `revtex/` holds the REVTeX 4.2 class
and bibliography-style files (LPPL, from TeX Live 2023) for installations without REVTeX; `build.sh` uses them.

The AI disclosure, the human-effort statement and the acknowledgements follow the title page, as required by
PSI's publication guidelines. The verification package cited as Ref. [Pkg] is [`../../verification/`](../../verification),
and the Lean formalization named in the AI disclosure is [`../../lean/`](../../lean).
