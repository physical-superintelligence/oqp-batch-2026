#!/bin/sh
# Builds main.pdf. REVTeX 4.2 is used from the TeX installation if present, else from ./revtex (LPPL, TeX Live 2023).
set -e
cd "$(dirname "$0")"
export TEXINPUTS=./revtex: BSTINPUTS=./revtex:
pdflatex -interaction=nonstopmode main >/dev/null
bibtex main >/dev/null
pdflatex -interaction=nonstopmode main >/dev/null
pdflatex -interaction=nonstopmode main
