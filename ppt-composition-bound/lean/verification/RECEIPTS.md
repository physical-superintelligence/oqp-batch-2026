# Verification receipts

Checked commit: `65516ce896a353fa97eee7576bbcdd862f9123d7`.

Both checks below ran on fresh remote Linux machines (Lean `v4.35.0-rc4`, Mathlib `1b3c4196`) on a
snapshot of that commit made with `git archive`, so uncommitted files could not enter; both runs used
the same snapshot. A verification harness (a build, an axiom audit and a kernel replay script) was
added to the snapshot for these runs only; it is not part of this repository.

| Run | Job id | Started | Verdict |
|---|---|---|---|
| Fresh build, axiom audit, closure replay, harness controls | `vm-20261014T135023Z-4dd3190e7fa8` | 2026-10-14 13:50 UTC | `BUILD CHECKS PASSED` (exit 0, 201 s) |
| `lake comparator --paranoid` | `vm-20261014T135027Z-4fe8951824c9` | 2026-10-14 13:50 UTC | `COMPARATOR CHECKS PASSED` (exit 0, 803 s); log ends `Your solution is okay!` |

## Fresh build and axiom audit

`lake build +Solution` from a clean checkout, then a fresh traversal of each theorem's dependencies
(independent of Lean's cached axiom collection):

| Theorem | Axioms |
|---|---|
| `PPTCompositionBound.choi_isCompletelyPositive_iff` | Classical.choice, Quot.sound, propext |
| `PPTCompositionBound.choi_isEntanglementBreaking_iff` | Classical.choice, Quot.sound, propext |
| `PPTCompositionBound.choi_isPPTMap_iff` | Classical.choice, Quot.sound, propext |
| `PPTCompositionBound.compList_pair` | Classical.choice, Quot.sound, propext |
| `PPTCompositionBound.compose_at_least_ppt_maps_entanglementBreaking` | Classical.choice, Quot.sound, propext |
| `PPTCompositionBound.compose_ppt_map_interleaved_entanglementBreaking` | Classical.choice, Quot.sound, propext |
| `PPTCompositionBound.compose_ppt_maps_entanglementBreaking` | Classical.choice, Quot.sound, propext |
| `PPTCompositionBound.ebIndex_id_eq_top` | Classical.choice, Quot.sound, propext |
| `PPTCompositionBound.ebIndex_le_of_isPPTMap` | Classical.choice, Quot.sound, propext |
| `PPTCompositionBound.exists_posSemidef_not_isSeparable` | Classical.choice, Quot.sound, propext |
| `PPTCompositionBound.id_not_entanglementBreaking` | Classical.choice, Quot.sound, propext |
| `PPTCompositionBound.transposeMap_isCompletelyCopositive_not_isCompletelyPositive` | Classical.choice, Quot.sound, propext |
| `PPTCompositionBound.zero_map_isPPTMap_and_ebIndex_eq_one` | Classical.choice, Quot.sound, propext |

Kernel replay: the dependency closure of the thirteen theorems (66,049 declarations) was
replayed into an empty environment by Lean's kernel at trust level 0
(73 s); no unsafe or partial declarations; axioms in the closure:
propext, Classical.choice, Quot.sound. The harness's own positive and negative controls (a forged
proof, an extra axiom, unsafe and partial roots) behaved as expected: `PASSED`.

## Comparator

`lake comparator --paranoid` with this repository's `comparator.json` (thirteen theorem names, permitted
axioms `propext`, `Quot.sound`, `Classical.choice`, no definition holes). All six kernel modes
accept: Lean paranoid, lean4lean, nanoda, con-leche, con-ron, Lean default. Kernel lines of the log:

```text
Running Lean paranoid kernel on solution
Lean paranoid kernel accepts the solution
Running lean4lean kernel on solution
checked 64622 declarations
lean4lean kernel accepts the solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running con-leche kernel on solution
con-leche: accepted 64625 declarations (--verified)
con-leche kernel accepts the solution
Running con-ron kernel on solution
con-ron: accepted 64625 declarations (--verified)
con-ron kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

## Axiom pin

`PPTCompositionBound/Audit/FinalCheck.lean` pins the output of `#print axioms` for each of the 13
theorems with `#guard_msgs`, and `lake build` builds it. The development build `20261014T133036Z-009b3c4620d9`
(`lake build PPTCompositionBound Challenge Solution`, the default targets, on the same Lean sources and
Lake files as the checked commit, byte for byte) built it with every pin passing (exit 0,
165 s). A control build, `20261014T133058Z-b16df93cb701`, added two temporary probes
that are not part of this repository: a pin expecting a wrong axiom list, and a theorem that uses an
extra axiom under the standard pin. Both failed the build on `#guard_msgs`, as intended.

## Pipeline controls

The same pipeline (identical `scripts/check.py`, `scripts/Audit.lean`, `scripts/Replay.lean` and
`lean-toolchain`, by SHA-256) was tested on 14 October 2026 in the batch-wide controls run
`vm-20261014T070106Z-9ef60cb2ed7c` (`PIPELINE CONTROLS PASSED`). It showed that the pipeline rejects a
wrong statement (Comparator: "Challenge and solution theorem statement do not match"), an extra axiom
(Comparator: "Illegal axiom detected") and a forged proof (rejected by all six kernel modes), while an
honest control is accepted.

## Hashes

Source snapshot hash computed by the harness (Lean sources and frozen statement files):
`b20e2eabaf62682b4d2450f358e675d988fef7f7b79360508310e0123b9aeeec` (identical in both runs).
SHA-256 over the tracked files of the checked commit (as computed by the snapshot tool):
`6bcfec4bb0b018363d0802129b751cafd4085de8138fe8650a8d623776dc192e`.

Every file of the checked commit, as checked (each equals `git show 65516ce896a3:<file>`):

| File | SHA-256 |
|---|---|
| `.github/workflows/ci.yml` | `60579f392498625a58f033ff6ea42a2e5a742002cd6b4d776a3e5ead062ebd4d` |
| `.gitignore` | `df4c95c92648367ad1c9ca1646f9d227d9577e07d1ff069f2aeddb8614faf217` |
| `CITATION.cff` | `2e72446cb68f15b8ee10edc57119c7a6a9a39d7c8aaf18b3fbedbe1b98a446e4` |
| `Challenge.lean` | `7884d35d4686261c2283024b300265ee3a311f4a9a7108c80cff3caef4544f84` |
| `Gemfile` | `c0197db488ffa8e154edea20a26fa7a1c1c3e89675dfce43e72c16831966dd9b` |
| `Gemfile.lock` | `d93caad3b41ab81138c1770dcde1415ac9aa47e8e469ea25b3f876a9f3d2cdff` |
| `LICENSE` | `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |
| `NOTICE` | `c88b9b9bdc8becd153d70bae61b475533a76c45c1ef830256e2fc94047d194b5` |
| `PPTCompositionBound.lean` | `14a58fac5dfbd311f29fe64394cb058e21f2513c101b919a45fa437c50908dc4` |
| `PPTCompositionBound/AtLeast.lean` | `1c030fecc688b96cfe9a60239a710dd91a802cd4ac39694f3360e06fe3aa8b86` |
| `PPTCompositionBound/Audit/FinalCheck.lean` | `0e08797b0289724b40f24cdd2044369137033f12403391669d215ea563f40e33` |
| `PPTCompositionBound/ChoiBridge.lean` | `6c1dd8bbe0258b24c8ba4240c72576de6c790cf4e50ea75a21d6d43ec7376866` |
| `PPTCompositionBound/CompatibleRangeTransport.lean` | `fb011c05adaaad9c0302c792a0a4beca49c377a6e638b42914226a6d458e095b` |
| `PPTCompositionBound/Counterexample.lean` | `320cba05e0a60087a8f5ca468208150e321d95f20bdc569987ea739cc798d31e` |
| `PPTCompositionBound/Defs.lean` | `1b56bd723ed6978c823b2dbba4d2d088d4b2eaa7ed063b82c117a41cd85c8703` |
| `PPTCompositionBound/ForMathlib/PositiveRankOneCoefficient.lean` | `91d2500d18c3b36aa7d23996c2baf60cb5ba6344fbd4fdd339fcd2ba88f9ab49` |
| `PPTCompositionBound/ForMathlib/PositiveRankOneSubtraction.lean` | `a555a99614995f912393be95f6063475585c74bcee78ad58b58ec9ab56504e42` |
| `PPTCompositionBound/ForMathlib/PseudoInverse.lean` | `494905bbb752d048d8b306943a8bfff386f1066a1bed0e8b643592d66b138a3c` |
| `PPTCompositionBound/ForMathlib/RankFactorization.lean` | `e6e1ceb18d58d3191246be2044a3d8689e39566325c5d9e9a3bdc24abc508fc1` |
| `PPTCompositionBound/ForMathlib/SVDComponents.lean` | `8565e4ac257d3cfda372e0d915307af4491e2de43834cbbcd8392f0ade877b69` |
| `PPTCompositionBound/ForMathlib/SchmidtBridges.lean` | `5ff2f8e38513e0d9392b4def4802a560ce9b127fe1c240926791a0ea876af0da` |
| `PPTCompositionBound/ForMathlib/SingularValueDecomposition.lean` | `f70b9d87c48293bd20068465062b191819297738eff3a41465b6db90cd6401dd` |
| `PPTCompositionBound/ForMathlib/SupportedSVD.lean` | `a78eceec91dd498a6cb158e4f2bb3d988da5857e788640fc41b0d2c501c3d6fc` |
| `PPTCompositionBound/ForMathlib/ThinSingularValueDecomposition.lean` | `e155cb123485d6fd0d321b4c008da070e053f002475fd612b907114e78db3d92` |
| `PPTCompositionBound/ForMathlib/TwoUnitaryFormula.lean` | `9c491d5673a02956afc7cd9317ce1bf9141ed1619df214bb82b0b7304520749b` |
| `PPTCompositionBound/ForMathlib/UnitaryEigenbasis.lean` | `d20b7bdebebcc8e0e98990e31effb7a98d0e82aab3b29f9f51173aa8efae9a92` |
| `PPTCompositionBound/ForMathlib/UnitaryResolution.lean` | `21f75c0963a8575ae1b53c9e825e825e85c895e500b1d117f274d8109bb0a5b9` |
| `PPTCompositionBound/GurvitsBarnum.lean` | `6e3ea3f1840b7538b8212ab3b153aef174fe76aa9a2a28a5790b75a492eb63c4` |
| `PPTCompositionBound/GurvitsBarnumCore.lean` | `bd44f499a9bcb5df333e1cadb93e241a42e717e6ee71d6aadb5f667826bca2cd` |
| `PPTCompositionBound/GurvitsBarnumSVD.lean` | `b04421e04ddf6d1f77f08bca489b69e4b3c1ed18a374dbfb611ad57b1ae98870` |
| `PPTCompositionBound/Iteration.lean` | `0c41487f7bef2e083dfae1eaced9bf61ae4ff2baf354b5bc17dcbd12569a8a3e` |
| `PPTCompositionBound/Lift.lean` | `bfbc4fd33be47ef74d7a6c5893d94ef87ce2fd6814158231f10e29e2dcb80a25` |
| `PPTCompositionBound/Main.lean` | `ad62bc131c731a1a65bbd9b45b45ce45ad9b68af047c1c2ec9dfea874272ce57` |
| `PPTCompositionBound/Maps.lean` | `0b43679d390938c82011577acfb0042b93b9475c277226837189422dc7d23ddb` |
| `PPTCompositionBound/NonTrivial.lean` | `21bfa6ce66cee3ce71d5d7d90ca7d6ddd9e2934109e33cd981e1ce6304c72120` |
| `PPTCompositionBound/PPTDecomposition.lean` | `3b2ecd7c28de5301bd788a43b9255b0a4428f015bb9ac614602a020f53c512f5` |
| `PPTCompositionBound/PPTDecompositionSVD.lean` | `6b1bce2a9ba078e76d09498308d28ef20a5efdf46e68c9cf721f084c8fa222fe` |
| `PPTCompositionBound/PPTSubtraction.lean` | `cde16295fa0bda9a9741524782cf79e9d0cc8b831d9a36c0fbb12629309e3810` |
| `PPTCompositionBound/Pair.lean` | `c50a92147f18309b406df8e088acdc4fe6f85770be0efec35536e5b088efd531` |
| `PPTCompositionBound/PairLemma.lean` | `f24d85ff9265e5929ff718de3425eb2fc3ad49085a9c0aa4264b00c62aa8bb95` |
| `PPTCompositionBound/QubitBlocks.lean` | `dbed573b7e93fb1d67e6621042dd69f43160f0842a284a11fd4752556d709986` |
| `PPTCompositionBound/QubitNormalization.lean` | `490937bfdf6d2bf4f7ab52783bb464a77581ef4514cd7a8a53796bfea2ffcdc5` |
| `PPTCompositionBound/Reduction.lean` | `7f569fa96235499d54ef8810e13280e59040538ef5ba6d63ef5b9b39abf81bfa` |
| `PPTCompositionBound/SchmidtDecomposition.lean` | `a23ff77056e2ac77583af6be59c9f0c504e12c952b883f2408d4581ae573f625` |
| `PPTCompositionBound/SchmidtFacts.lean` | `98daa469c9a3290fd4372383f7bfb2ae8a52eef61b0a047411d078829eb1f8cc` |
| `PPTCompositionBound/SchmidtNumber.lean` | `1fe32eb71c5294767b2d1494f3326981b0cb61439a1420bbf2c903cf515f497b` |
| `PPTCompositionBound/Separable.lean` | `e4c86fff93d629ae8b6d3fc49bda5625d267c0b532c15b451dade0c5aafe37e4` |
| `PPTCompositionBound/SeparablePure.lean` | `d661554d71b71f9993d2af05b56758470caed2a3f54a9f143c1a65823b561fa7` |
| `PPTCompositionBound/TensorMaps.lean` | `716d6d3e57dd57fccce0f653f2d105cd5beadc7139785e72eff6fa7a4a9371f2` |
| `README.md` | `29d76f6a933ec233dfc0252b208d854e0693f7e0c450479fc69c8f62d2ca4118` |
| `Solution.lean` | `d31c2aea17a80f5cff37906fb922d6e5c873950b8ccc75cded2a11e4ac695226` |
| `comparator.json` | `ba8aa0e78ca3b65088a257ec3b27580260017718422e0060b7ef560056f2e1cc` |
| `docs/FIDELITY.md` | `54d5a55bc76607171a20854a4fb8dce34d0c89d25db47e994788e3dc93c16590` |
| `docs/OQP_STATEMENT.md` | `f753ba6cb25f84cc0484bc8713eeb1d2e72e0dc3b9cb3c224988868047f9eb75` |
| `formalization.yaml` | `cd4ffe4bb558ff30585fb8d5a6c831fb3b096547cce18e27aa228bc9f0f8e506` |
| `lake-manifest.json` | `f0151289d7e5b19cee0e83e16609bc33b816ec4a092579c4df21c9bffee67787` |
| `lakefile.toml` | `1e0f253f20969684172ba6c0900d9544be37e316aa510ebcb34356ede6c60df1` |
| `lean-toolchain` | `8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7` |
| `paper/README.md` | `a3b8c573f1d2af488acd4937d355a1ae023983eb1c2b830df595196ac351d5f3` |
| `scripts/check-lean-sources.py` | `6919911f9905fcc9f01cac96e8c98a348a192a5550a10d127b0b3ced2d74bc5a` |
| `scripts/validate-formalization.rb` | `47eeb73febf48a2e23036e67f3223ea0562604139a7e97723c70cc4d5c269782` |
| `scripts/verify-comparator.sh` | `4fefa0e6c779448143b3164f56e96c3b6f719de67da335fa445127ab55f9b1e2` |
| `test/validate_formalization_test.rb` | `18801495c735d5ef93848b7ca045d44e71f11081e14a6ebed21159154d9177f8` |
| `verification/RECEIPTS.md` | `f357f6a36aa42f890681170b355c991d97b43e77d7379f3bd48d9555d13adc1a` |

## Logs kept in this repository

| File | SHA-256 |
|---|---|
| `verification/logs/check/receipt.json` | `a4a4aab4b4f39802db002e5a8c96e440a1e35b7cb9597b15eff1796ca3db58ae` |
| `verification/logs/check/axioms.log` | `e39869f4ee61e0ad25b04b540a0f9074a4e7772eab3d43ff9f753833a5af099f` |
| `verification/logs/check/kernel-replay.log` | `07f170b0ee2dd87d89817877f70c976f99966a26046b159c0c28ed1615275e2f` |
| `verification/logs/check/build.log` | `bfcdbed4155991aaecae9a159e323b31254abeb5d18f89e7a986dfe54df259ae` |
| `verification/logs/comparator/receipt.json` | `23be69ee16339fd2f2df54f3220fc8431c2788a4217f5e4281da8bdbe55ac912` |
| `verification/logs/comparator/comparator.log` | `f54deb6fe4a37764c2694036ff3abbd1b6b31d5026ce703c9f24f648448ca870` |

The harness writes `"status": "NOT VERIFIED"` and `"independent_semantics": "NOT ASSESSED BY THIS
SCRIPT"` into every receipt by design: it checks proofs, not whether the statements say what the paper
says. The verdict is the `check_result` field. Statement fidelity is discussed in
[docs/FIDELITY.md](../docs/FIDELITY.md).

Commits after `65516ce896a3` change only this file and `verification/logs/`; check with
`git diff --stat 65516ce896a3 HEAD`.
