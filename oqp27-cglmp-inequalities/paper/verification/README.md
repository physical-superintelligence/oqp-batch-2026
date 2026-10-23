# Verification scripts

Two Python 3 scripts accompany the paper "The optimal CGLMP measurements on maximally entangled states". Both scripts use exact arithmetic and only the Python standard library, and both need Python 3.9 or later. Run both commands from the `paper/` folder. Each script exits with status 0 when every check holds and with status 1 when some check fails. Equations are named by their labels in the paper's LaTeX source. Both scripts were written at PSI by an AI model, Anthropic's Claude Opus 5.5 in Claude Code, following the computations printed in the paper; each recorded output gives the script's SHA-256 and the date, platform and Python version of its run.

## verify_coefficients.py

**Checks:** part (ii) of the lemma "Bounds on the error coefficients" (`lem:scalar`), namely the inequality `eq:finitecondition` for all 2,080 pairs (d, k) with 2 ≤ d ≤ 65 and 1 ≤ k < d. The script encloses the error coefficients e_{d,k} (`eq:finiteeseries`, `eq:finitetail`) and the loads l_{d,k} (`eq:load`) by interval arithmetic with exact rational endpoints, using the data of Table `tab:intervals`; as in the paper, the enclosure of π is rounded outward to 80 decimal places and the enclosures of r_n to 60. The script also confirms the values printed in the paper: the normalized margin is at least 1935/10^4 > 1/6, the worst dimension is d = 7, and the certified minimum normalized margin exceeds 0.19354436777798498. The option `--control C1|C2|C3` runs a deliberately corrupted version of the check, which must fail. When the gmpy2 package is installed, the script uses gmpy2, with identical results; the recorded run used the standard library alone.

**Command:** `python3 -I verification/verify_coefficients.py`

**Run time:** about 5 seconds (5.0 s on the recorded run, in one process). The option `--jobs N` spreads the values of d over N processes.

**Expected final line:**

```
All assertions hold: 2080 of 2080 inequalities eq:finitecondition certified; normalized margin >= 1935/10^4 > 1/6 for 2 <= d <= 65.
```

**Recorded output:** `verification/verify_coefficients.out`: the command, the date, the Python version, the full output and the exit status of the run on 23 October 2026 (macOS, Python 3.9.6, standard library only).

## verify_circulation.py

**Checks:** the two identities of the appendix "The circulation sum of squares" (`app:circulation`):

- `eq:Cexpansion`, the expansion of the circulation C_ijk with the six rows of Table `tab:circulation`;
- `eq:circulationSOS` for both signs, sigma = +1 and sigma = -1, together with the positivity of the weights 1, 3, 3 and 7/3 + 2 sigma on the right side.

The script also checks the step P + O = p_ij + p_jk + p_ik (`eq:forbidden`, `eq:forbiddenspectral`). With the two identities, the step gives `eq:circulation`.

The check is symbolic, not a sample. Every quantity is a combination of traces of words in the twelve spectral projections E_{s,l}. The words are reduced with the relations of projection-valued measures alone (E† = E, E_l E_m = δ_lm E_l and Σ_l E_l = I at each site, no relation between sites) and with the properties of the normalized trace (cyclic, tr(X†) = conj tr(X), tr(I) = 1). The two sides of each identity are then compared cyclic word by cyclic word, with exact Gaussian-rational coefficients. Equal coefficients prove the identities for every matrix size. The script also runs deliberately corrupted versions of the identities (each sign of Table `tab:circulation` flipped in turn, and the weight 7/3 replaced by 2) and requires every corrupted version to fail. An exact 5 × 5 matrix example cross-checks the word arithmetic.

**Command:** `python3 -I verification/verify_circulation.py`

**Run time:** under one second.

**Expected final line:**

```
All checks hold: eq:Cexpansion is an identity, and eq:circulationSOS holds with positive weights for sigma = +1 and sigma = -1.
```

**Recorded output:** `verification/verify_circulation.out`: the command, the date, the Python version, the full output and the exit status of the run on 23 October 2026 (macOS, Python 3.14.6).
