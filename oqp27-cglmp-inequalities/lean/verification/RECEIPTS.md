# Verification receipts

Checked commit: `d45a91a3cd8e8488b023433dd7feca95fca272a7`.

Both checks below ran on fresh remote Linux machines (Lean `v4.35.0-rc4`, Mathlib `1b3c4196`), each
with 16 CPU cores and 128 GiB of memory, on one archive of that commit made with
`git archive`, so uncommitted files could not enter. All 492 tracked files of the commit are
byte-identical to the corresponding files of that archive. A verification harness (a build, an axiom
audit and a kernel replay script) was added to the archive for these runs only; it is not part of this
repository.

| Run | Job id | Started | Verdict |
|---|---|---|---|
| Fresh build, axiom audit, closure replay, harness controls | `vm-20261014T145056Z-584b96f2299a` | 2026-10-14 14:51 UTC | `BUILD CHECKS PASSED` (exit 0, 2159 s) |
| `lake comparator --paranoid` | `vm-20261014T145100Z-abd9d766a205` | 2026-10-14 14:51 UTC | `COMPARATOR CHECKS PASSED` (exit 0, 5055 s); log ends `Your solution is okay!` |

## Fresh build and axiom audit

`lake build +Solution` from a clean checkout, then a fresh traversal of each theorem's dependencies
(independent of Lean's cached axiom collection):

| Theorem | Axioms |
|---|---|
| `OQP27.bgp_facet` | Classical.choice, Quot.sound, propext |
| `OQP27.bgp_no_fusion` | Classical.choice, Quot.sound, propext |
| `OQP27.bgp_no_signalling_violation` | Classical.choice, Quot.sound, propext |
| `OQP27.bgp_not_cglmp_four` | Classical.choice, Quot.sound, propext |
| `OQP27.bgp_relative_interior_point` | Classical.choice, Quot.sound, propext |
| `OQP27.cglmp_local_bound` | Classical.choice, Quot.sound, propext |
| `OQP27.cglmp_witness_tolerance` | Classical.choice, Quot.sound, propext |
| `OQP27.fourier_attains_cglmp_value` | Classical.choice, Quot.sound, propext |
| `OQP27.fourier_projectors_pvm` | Classical.choice, Quot.sound, propext |
| `OQP27.noise_separation_955` | Classical.choice, Quot.sound, propext |
| `OQP27.partB_kl_discrimination_not_optimal` | Classical.choice, Quot.sound, propext |
| `OQP27.partB_maximizers_are_fourier_phase` | Classical.choice, Quot.sound, propext |
| `OQP27.partB_noise_resistance_not_optimal` | Classical.choice, Quot.sound, propext |
| `OQP27.statistical_separation` | Classical.choice, Quot.sound, propext |
| `OQP27.tensor_chsh_rank_one_pvm` | Classical.choice, Quot.sound, propext |
| `OQP27.tracial_table_physical` | Classical.choice, Quot.sound, propext |

Kernel replay: the dependency closure of the sixteen theorems (85,202 declarations) was
replayed into an empty environment by Lean's kernel at trust level 0
(518 s); no unsafe or partial declarations; axioms in the closure:
propext, Classical.choice, Quot.sound. The harness's own positive and negative controls (a forged
proof, an extra axiom, unsafe and partial roots) behaved as expected: `PASSED`.

## Comparator

`lake comparator --paranoid` with this repository's `comparator.json` (sixteen theorem names, permitted
axioms `propext`, `Quot.sound`, `Classical.choice`, no definition holes). Kernel lines of the log:

```text
Running Lean paranoid kernel on solution
Lean paranoid kernel accepts the solution
Running lean4lean kernel on solution
checked 83685 declarations
lean4lean kernel accepts the solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running con-leche kernel on solution
con-leche: accepted 83688 declarations (--verified)
con-leche kernel accepts the solution
Running con-ron kernel on solution
con-ron: accepted 83688 declarations (--verified)
con-ron kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

## Axiom pin

`CGLMPBounds/Audit/FinalCheck.lean` is part of the default `lake build`; its `#guard_msgs` checks pass
only if `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for each theorem of
`comparator.json`. It was built in the development build `20261014T144820Z-f9220f176668`
(2026-10-14 14:48 UTC, `lake build CGLMPBounds Challenge Solution`, exit 0, log line
`Built CGLMPBounds.Audit.FinalCheck`), whose 474 Lean and Lake files are byte-identical to those of
the checked commit.

## Pipeline controls

The pipeline itself was tested on 2026-10-14 in a separate run on the same VM image,
`vm-20261014T070106Z-9ef60cb2ed7c` (`PIPELINE CONTROLS PASSED`, exit 0), with small disposable
fixtures: an honest proof was accepted by all six kernel modes; a wrong statement was rejected
("Challenge and solution theorem statement do not match"); an extra axiom was rejected ("Illegal axiom
detected"); a forged proof was rejected by all six kernel modes.

## Hashes

Source snapshot hash computed by the harness (Lean sources and frozen statement files):
`73532f5a5e45ce9a9718cb0472c0ace471c92d1b0d3b2a63dff7cc1c1d72c65f` (identical in both runs).
Aggregate hash of the 492 tracked files of the checked commit, the SHA-256 of
`json.dumps({path: sha256(content)}, sort_keys=True)` (Python, default separators):
`9f8287095497724df44175f6f9f70def948b24df95825b3b2b2ec300e8c3593a`.

| File at `d45a91a3cd8e` | SHA-256 |
|---|---|
| `Challenge.lean` | `ee605c4ae57c7277ae8f27764f8a216ae08228f61987cf1b1f3a6fb167e8785d` |
| `Solution.lean` | `97220f2b19c71582381e9bc8fd10a6132f7428c193a89744ae1cd947bfefc6c9` |
| `comparator.json` | `c7259aecf9d4b63d87ee1eb9eb563f31d1d16daddb168bbb47b4f5e2a348af5a` |
| `lakefile.toml` | `a6ea02ba20a36088cd41083cc0627f8853cf1606861351007ebe8f92904c4014` |
| `lake-manifest.json` | `ea388d843e65bfb1c57f0dc84133864ecbcde932c23d9f7c12d07d5be9813b08` |
| `lean-toolchain` | `8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7` |
| `CGLMPBounds.lean` | `afded13ae7badcd9a0948ec69dc7999fc8a71f1298cf3981e9e0c0d4c5c536dd` |
| `docs/OQP_STATEMENT.md` | `438e73a64130d289b6b35023a7e0870e80f87f136990f20d0e10352bb6bb7e10` |

## Logs kept in this repository

| File | SHA-256 |
|---|---|
| `verification/logs/check/receipt.json` | `724fa7641ca0e6426844bbcf742a97ff9d41a8cab118ee025dc365fd14da8c08` |
| `verification/logs/check/axioms.log` | `cb257da1805b9491f1be688b7261653292c7f99cb176e01565e61cd6717a78f1` |
| `verification/logs/check/kernel-replay.log` | `c42b3c51588fd8c01a320b64162d326284c9caf7014edeba29f33646b6a4d517` |
| `verification/logs/check/build.log` | `da3dc93a4349a609798ed4af73c0e09d318e01ffb58dc65d42543c643d67028d` |
| `verification/logs/comparator/receipt.json` | `06af890991b10cf31d543a92d1f0367c0cf1808278c835ef608c9f1711fff93f` |
| `verification/logs/comparator/comparator.log` | `4a19bda1edde11f1d426b0e9ab52c178026d4d3bb75eaf75e3731a1187a5a903` |

Every receipt written by the harness carries the fixed fields `"status": "NOT VERIFIED"` and
`"independent_semantics": "NOT ASSESSED BY THIS SCRIPT"`; the verdict of a run is its `check_result`
field. The correspondence between the statements, the problem and the paper is recorded in
[docs/FIDELITY.md](../docs/FIDELITY.md).

Commits after `d45a91a3cd8e` change only this file and `verification/logs/`; check with
`git diff --stat d45a91a3cd8e HEAD`.
