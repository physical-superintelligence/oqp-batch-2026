# Verification receipts

Checked commit: `6a91bb4b256579eb39f6a5f08f2cb0c1e9bc94e5`.

Both checks below ran on fresh remote Linux machines (16 CPUs and 128 GiB memory each; Lean
`v4.35.0-rc4`, Mathlib `1b3c4196`) on a snapshot of that commit made with `git archive`, so uncommitted
files could not enter; all 1,045 tracked files of the commit are byte-identical to the files of
the checked snapshot. A verification harness (a build, an axiom audit and a kernel replay script) was
added to the snapshot for these runs only.

| Run | Job id | Started | Verdict |
|---|---|---|---|
| Fresh build, axiom audit, closure replay, harness controls | `vm-20261021T092624Z-9ce4765285ef` | 2026-10-21 09:26 UTC | `BUILD CHECKS PASSED` (exit 0, 1368 s) |
| `lake comparator --paranoid` | `vm-20261021T092654Z-76867478b00e` | 2026-10-21 09:26 UTC | `COMPARATOR CHECKS PASSED` (exit 0, 2902 s); log ends `Your solution is okay!` |

## Fresh build and axiom audit

`lake build +Solution` from a clean checkout, then a fresh traversal of each theorem's dependencies
(independent of Lean's cached axiom collection):

| Theorem | Axioms |
|---|---|
| `VacuumBellSeparation.OQP12.corollary_1_2` | Classical.choice, Quot.sound, propext |
| `VacuumBellSeparation.OQP12.freeFieldVacuum_exists` | Classical.choice, Quot.sound, propext |
| `VacuumBellSeparation.OQP12.localAlgebra_open_nonabelian` | Classical.choice, Quot.sound, propext |
| `VacuumBellSeparation.OQP12.no_chsh_violation_far_apart` | Classical.choice, Quot.sound, propext |
| `VacuumBellSeparation.OQP12.no_chsh_violation_far_apart_uniform` | Classical.choice, Quot.sound, propext |
| `VacuumBellSeparation.OQP12.theorem_1_1` | Classical.choice, Quot.sound, propext |

Kernel replay: the dependency closure of the six theorems (90,515 declarations) was
replayed into an empty environment by Lean's kernel at trust level 0
(467 s); no unsafe or partial declarations; axioms in the closure:
propext, Classical.choice, Quot.sound. The harness's own positive and negative controls (a forged
proof, an extra axiom, unsafe and partial roots) behaved as expected: `PASSED`.

The default `lake build` target, which includes the axiom check
`VacuumBellSeparation/Audit/FinalCheck.lean` (a `#guard_msgs`-checked `#print axioms` for each
theorem above), was built from this commit on a fresh machine in run
`rr-20261021T092713Z-readme-8e181e` (21 October 2026; Ubuntu 24.04, 32 CPUs and 128 GiB memory), which
ran the commands under "How to check" in [README.md](../README.md) as written, on a `git archive` of the
commit: `lake build` built `VacuumBellSeparation.Audit.FinalCheck`, printed
`Build completed successfully (10045 jobs)` and exited 0.

## Comparator

`lake comparator --paranoid` with this repository's `comparator.json` (six theorem names, permitted
axioms `propext`, `Quot.sound`, `Classical.choice`, no definition holes). Kernel lines of the log:

```text
Running Lean paranoid kernel on solution
Lean paranoid kernel accepts the solution
Running lean4lean kernel on solution
checked 88928 declarations
lean4lean kernel accepts the solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running con-leche kernel on solution
con-leche: accepted 88931 declarations (--verified)
con-leche kernel accepts the solution
Running con-ron kernel on solution
con-ron: accepted 88931 declarations (--verified)
con-ron kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

## Pipeline controls

The pipeline itself was tested once for the whole batch, in run `vm-20261014T070106Z-9ef60cb2ed7c`
(14 October 2026, 07:01 UTC; `PIPELINE CONTROLS PASSED`, exit 0), on the same machine
image (`im-ETpjO6JBRMxjjmBJtV9h10`) and with the same harness scripts (`scripts/check.py`,
`scripts/Audit.lean` and `scripts/Replay.lean`, byte-identical) as the two runs above. On small
disposable test files, Comparator rejected a wrong statement ("Challenge and solution theorem statement
do not match"), an extra axiom ("Illegal axiom detected") and a forged proof (rejected by all six kernel
modes), and accepted an honest proof.

## Hashes

Source snapshot hash computed by the harness (Lean sources and frozen statement files):
`c892ad974d0b2a9ef55ad1dcf07e2e94dd0477e46d2911a4da12e19aa09272d2` (identical in both runs).
SHA-256 over the tracked files of the checked commit: `ff50c81643cd8a0420ae7228875be879d2524342fdeb917b734c6b90bf05b747`; this is the SHA-256 of the
JSON object that maps each tracked path to the SHA-256 of its contents (keys sorted, Python
`json.dumps(..., sort_keys=True)`).

| File at `6a91bb4b2565` | SHA-256 |
|---|---|
| `Challenge.lean` | `9fe84946f2e2048f856a9d357583f1df3f8cac6398c15a87b8db87c98ace8ad3` |
| `Solution.lean` | `624ce1fe71d5649a79ad202a2456362edba4dce296a99435ec973563efeedf5f` |
| `comparator.json` | `8486cc8791b88615f822a5b649ac68aa660c1765e764b8b97183d8b1203d7b06` |
| `lakefile.toml` | `60a8d52b624ee47e27bd6cee0fca00f837fbb73484508bdfe77ed761ef554709` |
| `lake-manifest.json` | `f65c377b57441bbaafbeecb919e7852d17bc8b8bc6e3f9dcc442a6d9d1a062f1` |
| `lean-toolchain` | `8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7` |
| `VacuumBellSeparation.lean` | `9f0cb56d7ab50757c9e4cffb0e765345755bbcfd52cfa8444a2d50bdc34be232` |
| `VacuumBellSeparation/FreeField/Defs.lean` | `02f3ae28ef1ff837125f90ed423257818acf1986a9ee2add978fb400f58217ad` |
| `VacuumBellSeparation/FreeField/OQP12.lean` | `1f90954e38b25cc9d286b4d503c7f81616d107b64d3bc86968773e2b6d33e434` |
| `VacuumBellSeparation/Audit/FinalCheck.lean` | `599710509e2ed2ae2fc0a2ad1c0edf1b4faa0244c3626b1a89723e9f6880ae6b` |

## Logs kept in this repository

| File | SHA-256 |
|---|---|
| `verification/logs/check/receipt.json` | `9db1b6e632f1204b66d133dd1d3488e9f2beba096ced9cb2f7877e74930d8c81` |
| `verification/logs/check/axioms.log` | `aecd2393c02e56f5159555144b2cdbdacf0cfff34067a7157150411bf5f08161` |
| `verification/logs/check/kernel-replay.log` | `6124ea2df8196b1f32d3ef1f54d62873ddd79685f81ddddfd7bd7d4b9516e5dc` |
| `verification/logs/check/build.log` | `10098e9829636076d3d8d629222a5b7fbf22b792d771633ad0b59b83466627fc` |
| `verification/logs/comparator/receipt.json` | `ea4aebc21c8122eb72053b174cc85859ba55baf3017c39b5c83e1fb56a660a1d` |
| `verification/logs/comparator/comparator.log` | `9ff67a386c048d9a06de84f1d30cc7eba92a40e5d58f702ea9c0afc205ea0770` |

The harness writes the fixed fields `"status": "NOT VERIFIED"` and `"independent_semantics": "NOT ASSESSED
BY THIS SCRIPT"` into every receipt by design: it checks the proofs, and its verdict is the
`check_result` field. The correspondence of the statements with the problem and the paper is in
[docs/FIDELITY.md](../docs/FIDELITY.md).

Between `c5970740ecbf`, checked on 14 October 2026, and the checked commit, 39 Lean files changed, in
comments only: with comments and whitespace removed, the code of each of these files is identical at
the two commits. `git diff --stat c5970740ecbf 6a91bb4` lists these 39 files and, besides them, only
this file and the six files of `verification/logs/`, which held the receipts of `c5970740ecbf`.

Commits after `6a91bb4b2565` change no Lean file and no build configuration; check with
`git diff --stat 6a91bb4b2565 HEAD -- '*.lean' lakefile.toml lake-manifest.json lean-toolchain comparator.json`,
which prints nothing.
