# Verification receipts

Checked commit: `787448536a506e69c3f15d953257f224f095c5eb`.

Every check below ran on fresh remote Linux machines (Lean `v4.35.0-rc4`, Mathlib `1b3c4196`) on a snapshot of that commit made with `git archive`, so uncommitted files could not enter; all 5,316 tracked files of the commit are byte-identical to the files of the checked snapshot (SHA-256 `4d6c6de6993ffc872970d0c65ca767d9713f298baa729216609bde362818a0ea`). A verification harness (a build, an axiom audit and a kernel replay script) was added to the snapshot for these runs only. Two harness files differ from the harness of the development repository: `scripts/Audit.lean` (`0c9fc1bd51f0`, the development file `a6c28f62a9c5` with a set of already visited subterms per audited theorem, which skips no constant of its result, and each theorem's walk run as its own task, the reports printed in the same order) and `scripts/source_inputs.py` (`82c7de974be8`, the development file `3ff28651cc7d` with one change: it accepts `meta` in `public meta import` lines).

| Run | Job id | Started | Verdict | Wall time | CPUs | Memory |
|---|---|---|---|---|---|---|
| Split build, stage | `split-20261020T171240Z-119ec5a17bac` | 2026-10-20 17:12 UTC | SPLIT STAGE BUILT | 4,957 s (1.4 h) | 6 | 344,064 MiB |
| Split build, stage | `split-20261020T184031Z-556c2642cc2f` | 2026-10-20 18:40 UTC | SPLIT STAGE BUILT | 4,925 s (1.4 h) | 8 | 344,064 MiB |
| Split build, stage | `split-20261020T200701Z-b6b3be529246` | 2026-10-20 20:07 UTC | SPLIT STAGE BUILT | 1,253 s (0.3 h) | 16 | 344,064 MiB |
| Split build, stage | `split-20261020T203001Z-49b0260e4627` | 2026-10-20 20:30 UTC | SPLIT STAGE BUILT | 4,015 s (1.1 h) | 8 | 344,064 MiB |
| Split build, final | `split-20261020T213838Z-0d55df765e94` | 2026-10-20 21:38 UTC | SPLIT BUILD AND AXIOM AUDIT PASSED; KERNEL REPLAY DELEGATED TO THE SHARDS | 23,030 s (6.4 h) | 8 | 344,064 MiB |
| Kernel replay shard heavy-01 | `split-20261021T040415Z-cb18f8251de5` | 2026-10-21 04:04 UTC | SPLIT REPLAY SHARD PASSED | 4,887 s (1.4 h) | 8 | 344,064 MiB |
| Kernel replay shard heavy-02 | `split-20261021T040437Z-8f3a6b877024` | 2026-10-21 04:05 UTC | SPLIT REPLAY SHARD PASSED | 7,310 s (2.0 h) | 8 | 344,064 MiB |
| Kernel replay shard heavy-03 | `split-20261021T040522Z-5bc34c85681b` | 2026-10-21 04:05 UTC | SPLIT REPLAY SHARD PASSED | 6,843 s (1.9 h) | 8 | 344,064 MiB |
| Kernel replay shard heavy-expansion-01 | `split-20261021T052949Z-12a91e57cf88` | 2026-10-21 05:30 UTC | NOT VERIFIED | 1,443 s (0.4 h) | 32 | 344,064 MiB |
| Kernel replay shard light-01 | `split-20261021T053008Z-90e12ae69561` | 2026-10-21 05:30 UTC | SPLIT REPLAY SHARD PASSED | 2,909 s (0.8 h) | 32 | 344,064 MiB |
| Kernel replay shard expansion-01 | `split-20261021T053031Z-3c23cfbbc719` | 2026-10-21 05:30 UTC | SPLIT REPLAY SHARD PASSED | 1,679 s (0.5 h) | 32 | 344,064 MiB |
| Kernel replay shard heavy-expansion-01-t12 | `split-20261021T060253Z-f576b42a9e2e` | 2026-10-21 06:03 UTC | SPLIT REPLAY SHARD PASSED | 16,942 s (4.7 h) | 32 | 344,064 MiB |
| Comparator (harness, --paranoid) | `vm-20261020T133308Z-317e5c78f5bf` | 2026-10-20 13:33 UTC | exit 2; stopped at the export of Solution: failed to read a .olean.private file (the machine's default memory-map limit) | 26,656 s (7.4 h) | 8 | 344,064 MiB |
| Comparator (README procedure) | `npt-worker-20261019-readme-20261020T133354Z-14051d574f67` | 2026-10-20 13:34 UTC | README BLOCK NOT PASSED; lines 1 to 4 passed (its lake build built FinalCheck); line 5 stopped at the export of Solution: failed to read a .olean.private file (the machine's default memory-map limit) | 26,268 s (7.3 h) | 8 | 344,064 MiB |
| Comparator (README procedure) | `npt-worker-20261019-readme-20261020T160438Z-083f2ff10326` | 2026-10-20 16:22 UTC | README BLOCK NOT PASSED; line 4 (lake build) stopped at 64 CPUs; Lean processes killed with exit code 137 | 3,332 s (0.9 h) | 64 | 344,064 MiB |
| Comparator (harness, --paranoid) | `vm-20261020T163337Z-bcbd2378b8c4` | 2026-10-20 16:34 UTC | exit 2; the build inside Comparator stopped at 32 CPUs; Lean processes killed with exit code 137 | 6,787 s (1.9 h) | 32 | 344,064 MiB |
| Split build, stage that stopped (rerun with fewer CPUs) | `split-20261020T163323Z-68c78d36ce19` | 2026-10-20 16:33 UTC | NOT VERIFIED; Lean processes killed with exit code 137 | 2,323 s (0.6 h) | 16 | 344,064 MiB |
| Statement-hash probes | `20261020T211108Z-67de6d378fbb` | 2026-10-20 21:11 UTC | IDENTICAL; control as required | 1,462 s (0.4 h) | 8 | 344,064 MiB |
| Pipeline controls (Comparator on disposable projects) | `vm-20261020T133335Z-6bb3c683fca2` | 2026-10-20 13:33 UTC | PIPELINE CONTROLS PASSED | 18 s (0.0 h) | 8 | 65,536 MiB |

Runs still going when this file was written, and not used in it: a second retry of the replay of the root module, with 8 Lean threads (`split-20261021T060232Z-85be88f86b05`); the harness's paranoid Comparator with the memory-map limit raised (`npt-worker-20261019-vmmap-20261020T211249Z-13c13ebca985`); the README procedure with the memory-map limit raised (`npt-worker-20261019-readme-20261020T210202Z-c99107a7d085`).

## Build and axiom audit

The build of the library and of `Solution` ran in stages from a clean checkout; the final stage then walked each theorem's dependencies afresh (independent of Lean's cached axiom collection):

| Theorem | Axioms |
|---|---|
| `ThreeCopyQutritWerner.Endpoints.qutritEndpointInequality` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.sharp_minimum` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.interior_minimizers` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.minimum_formula_unequal_dims` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.werner_three_three_copy_iff` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.werner_three_npt_not_three_copy` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.overlap_le_half` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.continuation_identity` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.formR_nonneg_rank_two` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.cutForms_nonneg_rank_two` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.three_copy_expectation` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.schmidtRank_vec` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.werner_state` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.werner_npt_iff` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.werner_three_one_copy_iff` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.werner_three_three_copy_of_gt` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.werner_three_not_three_copy_of_nonpos` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.werner_three_not_three_copy_of_le_third` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.interior_shape_attains` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.familyI_endpoint_zero_any_plane` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.endpoint_zero_rank_two` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.overlap_le_half_of_nonpos` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.overlap_le_half_of_le_third` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.filter_iff_rank_two_detectable` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.sharp_curve_attained` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.sharp_minimum_of_endpoint` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.minimum_formula_of_card_of_endpoint` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.interior_minimizers_of_endpoint` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.werner_three_three_copy_iff_of_endpoint` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.werner_three_npt_not_three_copy_of_endpoint` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.overlap_le_half_of_endpoint` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.formR_eq_proj` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.rank_raise_ptrace` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.three_copy_ppt_of_le_third` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.werner_two_half_separable` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.noisy_family_posDef` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.noisy_family_npt` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.sharp_minimum_isLeast_of_endpoint` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.zero_families_are_half_singular_zeros` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.qutrit_endpoint_of_certificate` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.noisy_family_three_copy_of_endpoint` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.projector_cut_identity` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.cutForm_two_plane_projector` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.two_plane_product` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.twoQubit_separable_iff_ppt` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.appendixC_input1` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.appendixC_input2` | Classical.choice, Quot.sound, propext |
| `ThreeCopyQutritWerner.Endpoints.appendixC_input3` | Classical.choice, Quot.sound, propext |

The default `lake build` target, which includes `ThreeCopyQutritWerner/Audit/FinalCheck.lean` (a `#guard_msgs`-checked `#print axioms` for each of the 48 theorems, which fails the build unless each depends on exactly `propext`, `Classical.choice` and `Quot.sound`), completed successfully in run `npt-worker-20261019-readme-20261020T133354Z-14051d574f67` (2026-10-20 13:34 UTC): line 4 of the README procedure, `lake build` from a fresh checkout, 26,112 s (7.3 h) on 8 CPUs with 344,064 MiB.

## Kernel replay

Every module of the import closure of `ThreeCopyQutritWerner` and `Solution` (15,121 modules, Lean's `Init`, `Std` and `Lean` and Mathlib included) was replayed by Lean's kernel (`leanchecker`, one module per process, loading its imports from the built files; the process for the root module `ThreeCopyQutritWerner` also replays every module whose name begins with `ThreeCopyQutritWerner.`, since `leanchecker` reads its argument as a module prefix) in 6 shard runs that passed (the table above also lists the replay run that did not pass); the coverage check found every module replayed with result OK and one build manifest (`b9fd17bfc3bb8bef75173c47fb2977c6948849c7aafb105302e1dfddf07cb61c`): `COVERAGE COMPLETE`. Its report is `verification/logs/replay/coverage.json`, with its inputs named by the final run's closure file and the shard receipts kept beside it.

## Statement check

No Comparator run on this commit passed (the Comparator rows of the table above: two stopped at the export of `Solution` on the machine's default memory-map limit, two had Lean processes killed with exit code 137 during their build). The statements were checked without Comparator, on the checked commit: `scripts/check-challenge-definitions.py` printed `1 verbatim blocks checked`; a build of the commit's files with probe modules added printed, for each of the 48 theorems, Lean's structural hash of its statement (`Expr.hash`, a 32-bit value) and, for every project constant reachable from the statements through types and definition bodies, its kind, universe parameters and hashes, once from `Challenge.lean` and once from `Solution.lean`: the two lists are identical, and a probe that negates one statement differs in exactly that statement's line. Hashes, not the expressions, are compared, and constants outside this project are not hashed (both files use the same pinned Mathlib). Together with the axiom audit, `FinalCheck` and the kernel replay above, these checks stand in for Comparator.

## Pipeline controls

Run `vm-20261020T133335Z-6bb3c683fca2` (`PIPELINE CONTROLS PASSED`), on the same machine image: on small disposable projects Comparator accepted an honest proof, blocked a write outside its sandbox, rejected a wrong statement, an extra axiom and a forged proof (rejected by nanoda and, without `--paranoid`, by Lean's default kernel).

The split build's own controls, on small test layouts with the same driver (`scripts/check_split.py`) and the audit file without the per-theorem tasks (`ab3e2ecff8c6`):

| Control | Job id | Expected | Result |
|---|---|---|---|
| honest (final) | `split-20261020T133443Z-05f9c83ff12a` | passes | as expected (exit 0) |
| axiom (final) | `split-20261020T133804Z-8c51ec81df0d` | planted axiom reported, check fails | as expected (exit 2) |
| sorry (final) | `split-20261020T133454Z-d5ce95b17d67` | refused at the contract preflight | as expected (exit 2) |
| sorryax (final) | `split-20261020T133457Z-585c3a3c0d7d` | sorryAx reported, check fails | as expected (exit 2) |
| tamper (stage) | `split-20261020T133500Z-3db18c7cc276` | stage passes | as expected (exit 0) |
| tamper (final) | `split-20261020T133636Z-7db967496827` | altered manifest refused | as expected (exit 2) |

## Hashes

Source snapshot hash computed by the harness: `00c4c3600eba8358005c71cf80666a1d9b003304c41e700258b04f4ed3c01899`.
SHA-256 over the tracked files of the checked commit: `b87d01d88e1dcfd8f786bbf3e9383db543aa260d271e142333466788a0263c5b`; this is the SHA-256 of the JSON object that maps each tracked path to the SHA-256 of its contents (keys sorted, Python `json.dumps(..., sort_keys=True)`); `SHA256SUMS` lists each file.

Build manifests (each stage saves `.lake/build` with a SHA-256 manifest; the next stage restores and checks it):

| Job id | Manifest in | Manifest out |
|---|---|---|
| `split-20261020T171240Z-119ec5a17bac` | `-` | `6aa92a1e79dd6c2eebc28adbea4c67674da0bf46baf7d51bfff7aad985cc02ff` |
| `split-20261020T184031Z-556c2642cc2f` | `6aa92a1e79dd6c2eebc28adbea4c67674da0bf46baf7d51bfff7aad985cc02ff` | `bb6de2573d3cab44b1d3ffcdaea61012988c7c9e499106f6caa4235dacd847d7` |
| `split-20261020T200701Z-b6b3be529246` | `bb6de2573d3cab44b1d3ffcdaea61012988c7c9e499106f6caa4235dacd847d7` | `b6216040db27dfbdeb0cbc82fe2b01033973624d54b4eb305d5e2375dca8dd10` |
| `split-20261020T203001Z-49b0260e4627` | `b6216040db27dfbdeb0cbc82fe2b01033973624d54b4eb305d5e2375dca8dd10` | `e176945f39c315adea488910557a2f93ee65da3307806f6cbfa8f1019ed18df9` |
| `split-20261020T213838Z-0d55df765e94` | `e176945f39c315adea488910557a2f93ee65da3307806f6cbfa8f1019ed18df9` | `b9fd17bfc3bb8bef75173c47fb2977c6948849c7aafb105302e1dfddf07cb61c` |

| File at `787448536a50` | SHA-256 |
|---|---|
| `Challenge.lean` | `e881c44a36f988402162a92230ad4c749386564e1046ebcf36e7d22072d6a178` |
| `Solution.lean` | `7926faa8a1790fa9b5c962b3420ffe362225ff95136c3c04f42a365e87a06049` |
| `comparator.json` | `62e305ab077a9937973a11e83a29520b862db0eefdbe687936bea2cf9170658b` |
| `lakefile.toml` | `082f56bba30fa106ca36a2e3ba3eaf333077fcf8a08eac5a0613c42772a48edc` |
| `lake-manifest.json` | `6310e24faaa98179abf730b3ac921cc322bf78accff322de6b299ab5be06159b` |
| `lean-toolchain` | `8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7` |
| `ThreeCopyQutritWerner.lean` | `2af462885ea8b66f5cd2d2b1720fc1a59e5f8d4c2cb08810ad2fa33a2569f1f0` |
| `ThreeCopyQutritWerner/Basic.lean` | `6b95dc950f67b7336d38e4fa9281d727744b07795c8c3404b7efbee91d0e43bf` |
| `ThreeCopyQutritWerner/Audit/FinalCheck.lean` | `7d820e328ced0467994a33eda7c5ee43453a7c552bddc58abcc30a1172c8dc25` |

## Logs kept in this repository

| File | SHA-256 |
|---|---|
| `verification/logs/final/receipt.json` | `521ed4fb5ce49a3d12fea60326fb48d5dfa67e2721383ec11581e6706910c8b4` |
| `verification/logs/final/axioms.log` | `5c2b30e6a4fdf957c39a735574b0bc8f700970fee721262a2d6a30885dbea455` |
| `verification/logs/final/build.log` | `b17b69121687f9c96af158893dcf157ee2c6fcbfa543ef58417516e4c31374b3` |
| `verification/logs/finalcheck/line-04.log` | `126dbd128c72ddb4bdf1cf55a15ad65ba79ae045365fe18d5f4175c6c25256fd` |
| `verification/logs/replay/coverage.json` | `4dd46fb85793f593cb6739bf468fa70a788e633185c49b850ee1ecee5b5319ba` |
| `verification/logs/replay/heavy-01-receipt.json` | `740460bc474dc0ef2706b12faac8f23247dddba6c2b1fb55da7f65907765d7e9` |
| `verification/logs/replay/heavy-02-receipt.json` | `7dd877cb28bc418b334ec65e029fcc9bad24dc0044c79bf3f9a1d1265f5116bc` |
| `verification/logs/replay/heavy-03-receipt.json` | `cd94a79d2371d5caf59fbe4073c28642f3d98e903685509f34e35b2e126b0844` |
| `verification/logs/replay/heavy-expansion-01-receipt.json` | `57fa09e292e3fdc4ca163f36f3670ac0e3f9d29c1c835b9e9f9623e9df2402c2` |
| `verification/logs/replay/light-01-receipt.json` | `aec36e3fa3064fc64cf0a6d4250670cae03b47f68f1208e8af54733ee2865cc1` |
| `verification/logs/replay/expansion-01-receipt.json` | `68a4ec50ad253e01703055fda4383a05119118083f1960729a553d0a8d581f7c` |
| `verification/logs/replay/heavy-expansion-01-t12-receipt.json` | `d55de15209f18ea9b91ccbded1aed2cfb71a3ab7c697e7d8a0ecb2a498f7defb` |
| `verification/logs/out-of-memory/npt-worker-20261019-readme-20261020T160438Z-083f2ff10326-line-04.log` | `820734e085893edeaa825b213ec81d0a2c26e7db7c30bf6831c91c1242ac1297` |
| `verification/logs/out-of-memory/split-20261020T163323Z-68c78d36ce19-build.log` | `ad7144cd71bf0ee7f7b66b50e26296a93a814447348f0e1abfd02d8fc7c49046` |
| `verification/logs/out-of-memory/vm-20261020T163337Z-bcbd2378b8c4-comparator.log` | `4fcbc3968c7bda5c2de098c23c1932127a7fac552a6fd3c96b82f4677360f1a6` |
| `verification/logs/statement-check/hash-probes-remote-output.log` | `9f370a3d7ba3e89bdad7419195da0e6f8ee2714db2d5a5691c2694e6ec525c05` |
| `verification/logs/statement-check/check-challenge-definitions.log` | `83c0881dd255273746af6e0d83e4217a0f6389060c0a43bb545ad31ae5c3a8fd` |
| `verification/logs/controls/pipeline-receipt.json` | `d269c64efef0ae8d339ee3e156ed96a29941edf826fbb3f87ff49b3bfa319437` |

The harness writes the fixed fields `"status": "NOT VERIFIED"` and `"independent_semantics": "NOT ASSESSED BY THIS SCRIPT"` into every receipt by design: it checks the proofs, and its verdict is the `check_result` field. The correspondence of the statements with the problem and the paper is in [docs/FIDELITY.md](../docs/FIDELITY.md).

Commits after `787448536a50` change only documents, metadata files, `.github/workflows/ci.yml`, the comments and messages of `scripts/verify-comparator.sh`, `test/validate_formalization_test.rb`, `SHA256SUMS` and files under `verification/`, never a `.lean` file, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` or a data file; check with `git diff --stat 787448536a50 HEAD`.
