# Verification receipts

Checked commit: `3e78c71a3666e793b8bc1efb19113873c652a9a1` (git tree `78466033054da01f027308af6ec257ce2ca5c317`; commit identifiers change if the history is
re-authored, tree and file hashes do not).

The checks below ran on fresh remote Linux machines (Lean `v4.35.0-rc4`, Mathlib `1b3c4196`,
8 cores, 64 GiB of memory). The fresh build and the Comparator run used a snapshot of the checked
commit made with `git archive`, with a verification harness (a build, an axiom audit and a kernel
replay script) added for these runs; the jobs' own file hashes equal the hashes listed below for
every file of the commit.

| Run | Job id | Started | Verdict |
|---|---|---|---|
| Fresh build, axiom audit, closure replay, harness controls | `vm-20261014T133808Z-75d63d739e2c` | 2026-10-14 13:38 UTC | `BUILD CHECKS PASSED` (exit 0, 204 s) |
| `lake comparator --paranoid` | `vm-20261014T133812Z-e5bdbba0fd6d` | 2026-10-14 13:38 UTC | `COMPARATOR CHECKS PASSED` (exit 0, 657 s); log ends `Your solution is okay!` |
| `lake build` of the default targets, with the axiom pin | `20261014T133335Z-1a92b132cba1` | 2026-10-14 13:33 UTC | exit 0 (167 s) |

## Fresh build and axiom audit

`lake build +Solution` (the library and `Solution.lean`) from a clean checkout: no errors and no
`sorry`. `Challenge.lean` is built in the Comparator run below, where its eleven `sorry` warnings
are the placeholders, one per statement. Then a fresh traversal of each theorem's dependencies
(independent of Lean's cached axiom collection):

| Theorem | Axioms |
|---|---|
| `CausalNonpurifiability.OQP43.dimension_dichotomy` | Classical.choice, Quot.sound, propext |
| `CausalNonpurifiability.OQP43.not_all_extensiblyCausal_purifiable` | Classical.choice, Quot.sound, propext |
| `CausalNonpurifiability.OQP43.ocb_process_not_extensiblyCausal` | Classical.choice, Quot.sound, propext |
| `CausalNonpurifiability.OQP43.ordered_processes_purifiable` | Classical.choice, Quot.sound, propext |
| `CausalNonpurifiability.OQP43.purifiable_causallySeparable` | Classical.choice, Quot.sound, propext |
| `CausalNonpurifiability.OQP43.purifiable_iff_transpose_formula` | Classical.choice, Quot.sound, propext |
| `CausalNonpurifiability.OQP43.swap_table_not_causal` | Classical.choice, Quot.sound, propext |
| `CausalNonpurifiability.OQP43.theorem_1_1` | Classical.choice, Quot.sound, propext |
| `CausalNonpurifiability.OQP43.valid_iff_channels_normalized` | Classical.choice, Quot.sound, propext |
| `CausalNonpurifiability.OQP43.white_process_purifiable` | Classical.choice, Quot.sound, propext |
| `CausalNonpurifiability.OQP43.wq_pauli_form` | Classical.choice, Quot.sound, propext |

Kernel replay: the dependency closure of the eleven theorems (58,130 declarations) was
replayed into an empty environment by Lean's kernel at trust level 0
(59 s); every declaration replayed; axioms in the closure:
propext, Classical.choice, Quot.sound. The harness's own positive and negative controls (a forged
proof, an extra axiom, unsafe and partial roots) behaved as expected: `PASSED`.

## Comparator

`lake comparator --paranoid` with this repository's `comparator.json` (eleven theorem names, permitted
axioms `propext`, `Quot.sound`, `Classical.choice`, no definition holes). All six kernel modes accept
the solution. Kernel lines of the log:

```text
Running Lean paranoid kernel on solution
Lean paranoid kernel accepts the solution
Running lean4lean kernel on solution
checked 56792 declarations
lean4lean kernel accepts the solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running con-leche kernel on solution
con-leche: accepted 56795 declarations (--verified)
con-leche kernel accepts the solution
Running con-ron kernel on solution
con-ron: accepted 56795 declarations (--verified)
con-ron kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

## Axiom pin in the build

`CausalNonpurifiability/Audit/FinalCheck.lean` runs `#print axioms` under `#guard_msgs` for each of the eleven
theorems of `comparator.json`, so `lake build` stops unless each depends on exactly
`[propext, Classical.choice, Quot.sound]`. Development build `20261014T133335Z-1a92b132cba1` ran
`lake build CausalNonpurifiability Challenge Solution` (the default targets) with this module and
finished with exit 0; its Lean sources and build files are byte-identical to those of the checked
commit (SHA-256 compared file by file).

## Pipeline controls

The pipeline itself was tested for the whole batch in run `vm-20261014T070106Z-9ef60cb2ed7c` (14 October 2026, verdict
`PIPELINE CONTROLS PASSED`), on the same machine image and with the same harness files and toolchain
as the fresh build and the Comparator run above. On small disposable fixtures it accepted an honest
proof and rejected a wrong statement (`Challenge and solution theorem statement do not match`), an
extra axiom (`Illegal axiom detected`) and a forged proof (rejected by all six kernel modes).

## Hashes

Source snapshot hash computed by the harness (Lean sources and frozen statement files):
`0a130b44e10693c03e90f10f335e5abb67ff636031ae4710574d0c0ed8d987f5` (identical in both runs).
SHA-256 over the tracked files of the checked commit (as computed by the snapshot tool):
`8a37fc2b2fb1af8c38bed70da6d241014f1992e48f8a33d021a3d89f72332e7d`.

| File at `3e78c71a3666` | SHA-256 |
|---|---|
| `Challenge.lean` | `2a95299010d6e7a32b45919cdce92e6518fea8a994d00639d0d10e8a0ec20783` |
| `Solution.lean` | `9fc3167593a06fc91d89ab7301cb0ce6bd3322d5a01eaccbbe50706fac303921` |
| `comparator.json` | `211df3def90439664bce2fb05641a9c3191ed3a267d9882e809b28a474ab281d` |
| `lakefile.toml` | `42ac2ad8594c695eb3384c11765be6c4ff8c10cb04e15cc7f29a22c9f8a0d102` |
| `lake-manifest.json` | `1335f65b84e10aa7e66f07d6d313d3567ab677f436b361ac5684c6e8337a2f9d` |
| `lean-toolchain` | `8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7` |
| `CausalNonpurifiability.lean` | `3780985a9688a0309b6813da1969b1e54901436e4fd7f0ec84d9d3d8778c4cf3` |
| `CausalNonpurifiability/Audit/FinalCheck.lean` | `66339671ee7145359353f11cbe8f2da4d753a0f47647714da1e6301ab31903ee` |

SHA-256 of every public file at `3e78c71a3666` except `verification/RECEIPTS.md` (at that commit a
one-line stub, replaced by this file); save the block to a file and run `sha256sum -c`:

```text
64a6cd6174f271e4169004889bfb82dad53ff360095c8068079c2b9d82ea0046  .github/workflows/ci.yml
df4c95c92648367ad1c9ca1646f9d227d9577e07d1ff069f2aeddb8614faf217  .gitignore
7b75caf1fb885d017167634b3b5399abd390ba59049eae69c6993bd51b4e1abd  CITATION.cff
3780985a9688a0309b6813da1969b1e54901436e4fd7f0ec84d9d3d8778c4cf3  CausalNonpurifiability.lean
66339671ee7145359353f11cbe8f2da4d753a0f47647714da1e6301ab31903ee  CausalNonpurifiability/Audit/FinalCheck.lean
04a51af6bf6c7a5f08db33f5743d488fe41d0df2253182886dbb93ce2c919d70  CausalNonpurifiability/BellCHSH.lean
e2b1931b891997ea5556b779fffec032a52a700755450c16554b1c5937997616  CausalNonpurifiability/Bias.lean
56e42f6ec429c51c6623cd659bc83179aa772c425685ebe756cf28138e9c5ee0  CausalNonpurifiability/Boundary/Dilation.lean
a0c4cb3352b7f904e96f6c99dc2aac09c3e86350822dc12def86b742cf2fbd17  CausalNonpurifiability/Boundary/Order.lean
b86567f28ad42bb77afae5b373d02639ebf192fe6c4f48924721f754ab29bc5b  CausalNonpurifiability/Boundary/Swap.lean
37e1aaaa8fed180cba26ab22e8b85bc8d4acc3e83d2e186e011c85a50f3707ed  CausalNonpurifiability/Boundary/Transpose.lean
0662e355d0f4bf41d92044dff660f8790b92fde4dd943eb8a911a81e02f8e42b  CausalNonpurifiability/Certificates/Qubit.lean
0cea61e4c664071b00eb2bd25e2e8b3eb0b5d76fdc5a057c7d00fa7da04e20e3  CausalNonpurifiability/Certificates/QubitCore.lean
4a43e2f40ab160d93dc9c568bdc5395fd2a070f5932f3ed9d82ce4ec83bdb249  CausalNonpurifiability/Certificates/Soundness.lean
83bb2b0dc0aabae62bdaea1f0b31912662fb64948ce06ee96e7163bf5fbb9c25  CausalNonpurifiability/Certificates/Witness.lean
a6cf95369cbd39f17562674bb65908376c69ca0e71835eccc84a6e4eecb22bc8  CausalNonpurifiability/Classes.lean
b5fe1c8fc234ac3619e5e145aa70dd002d9b2c5588bbf67837d20a07099f72bf  CausalNonpurifiability/Classical/Transport.lean
8eef1bef01dcc889c059ce4126fd4feaa2743090b25fb97c616a2d4c14c78eb9  CausalNonpurifiability/Data/Local.lean
1ab8fe4ab6e6ad6f0bbde2f8a2698e637591515994998dceda351cf1f0a05bb9  CausalNonpurifiability/Data/Qubit.lean
ccfa8dc37029bfdcff10bd1f39a89c8d0b6bff7fe4181493a0e36b4e851c3e39  CausalNonpurifiability/Data/QubitCore.lean
6187bc741005878b15775a0d069a0106598614b841776db8baa05b3e5f7619d6  CausalNonpurifiability/Definitions/BallCore.lean
76bef1af5d68d03ffc81a1994679c5e74cdcefb740702c6996c445f9ae16897c  CausalNonpurifiability/Definitions/Bias.lean
25eadc6f4874a8f77270f1467d57a5c32bb5c3ab42839253c3f521a4dfc90f3b  CausalNonpurifiability/Definitions/CausalProcess.lean
39c2d29a014b0495ee78e64d3d70a5558bde592281fd1c88a935ffa47700fe96  CausalNonpurifiability/Definitions/CausalProcessCore.lean
39f7141a1fed7854e84009cabb87fa42845f45c77acbc2dd060c024b26d3d278  CausalNonpurifiability/Definitions/Causality.lean
ee4dda6705f02c29b712fc8ea2840c25f864a9eadcbcd045f16a96ad09379c2d  CausalNonpurifiability/Definitions/Channels.lean
63347c15f10bc3dad8d308414725b71c5414f6d26bc1d6881335890f518692c3  CausalNonpurifiability/Definitions/ConvexForm.lean
caf72e7a105b6034b3c59f7ae7d3f0ca0c6f44a4bbbb930490a9cdfcf53ccea3  CausalNonpurifiability/Definitions/ConvexFormCore.lean
ecef1342e9bbfbcfc3777e8a5bc4308ec14763217693677d721990c59b7a3587  CausalNonpurifiability/Definitions/EffectCore.lean
cad4b5b6c56fc41e946c1a65b8a66df8d0ddbafe97bfaed0965379730cc393d7  CausalNonpurifiability/Definitions/ExtensibleGeneral.lean
a80d6bf8895055274a8d8f9953cea600c15200f90f145d2f9e141809f6bd3cef  CausalNonpurifiability/Definitions/HeisenbergCore.lean
a7ca94049f03f91abb6b48933d85e75da22437f591d16502a0dc36d2b24a700f  CausalNonpurifiability/Definitions/Hypotheses.lean
c556f06b56053d86cdae11e805708e58a73dfc38d9f09f6bc68d8d596e170539  CausalNonpurifiability/Definitions/Instruments.lean
3ff3c17e8bf93e231c91479c613b42ec5bf85299b6da8237621eb070884c4608  CausalNonpurifiability/Definitions/InstrumentsCore.lean
3a32acfc029cb86ac880771f6f831434e5296c9515a08a5f27f874f10193d280  CausalNonpurifiability/Definitions/LVEquations.lean
07728409ba662cdd6dfeecbb7397b9f6c14e90262b0f98dba984808f64a77f92  CausalNonpurifiability/Definitions/LinkAlgebra.lean
2c7259de0ca135e896998419a7792f296d5da185c1a1d3a577f1631889f52df3  CausalNonpurifiability/Definitions/OCB.lean
f79c1257b19b0b730edefc2a13e903459043878bf1dcc89889a245a1d3ce5577  CausalNonpurifiability/Definitions/OCBGame.lean
67b6a9bccc2a570509b1490d7f4ea98bfc31935be73e0809d60381e69207ef50  CausalNonpurifiability/Definitions/OrderedMarginal.lean
d178f19b76853aa6a45039e23c8e425027e7d7a60d2f1ab45bdf854aac61c603  CausalNonpurifiability/Definitions/OrderedMarginalCore.lean
a54aeda9b27083cb33b02cb6d2c0483eb87e468493dbf1234bc7e0af09c7a61e  CausalNonpurifiability/Definitions/PortsSwapCore.lean
d5d518f5b0f37a515f857f5dcde80bff4099cb50a45b0e15c47a8b17d9dbf354  CausalNonpurifiability/Definitions/Process.lean
1a5badc3562d63fdb445b65835634c7f77d7d36a379f689e200ee1ff5cf2c27f  CausalNonpurifiability/Definitions/ProcessCore.lean
a9345f35e39d2f8ae84d1e4ec150a4de980317039a50c0ec54ebe45e075f79af  CausalNonpurifiability/Definitions/ProcessFamily.lean
a4b8d3cc9d8376a4aa61cc742cfdf474d1817dd744a14b13e4a7c12f000d0908  CausalNonpurifiability/Definitions/ProcessSwapCore.lean
c1af43fc5ffc1c9f543c8cd09196988030ef845a0312b3267390edf7edd0ba2d  CausalNonpurifiability/Definitions/Purity.lean
9df53e74712d26919c4a74baae5667f9dcef2192bfd515d49fe0425c64426539  CausalNonpurifiability/Definitions/Separability.lean
d81b023252f8318d96c9f898eea55269d752627256a523478095b8969ab0cfa4  CausalNonpurifiability/Definitions/SeparationCore.lean
51f4c7f9bb27330f4b867c35cb855852dad13f7f8f92aa2d31c8d62cb1548d09  CausalNonpurifiability/Definitions/SharedInputMarginalsCore.lean
fa5a147e04238eab86f95c65616974c26a5a3b9fe80d8317a5d4589cfb521161  CausalNonpurifiability/Dichotomy.lean
29b932ef1973ab0bb912b93ba51c8ce630d82851c73232546e0d89f1b3b2ef87  CausalNonpurifiability/EC/Bridge.lean
7a2d57d7e9572da732eff3b4df82a3ba9425abfb4f24ee0b2635bb4fdecfe8b5  CausalNonpurifiability/EC/Components.lean
3c37dc7ab2068d50fe1f2a0b0c2ea8d3d0f92001f2f53181b5c0c47797af93d6  CausalNonpurifiability/EC/Compression.lean
c905c7c37bcec7c5cafd823eef2494f459db1bc2f977b0a3e41b41b5ea3f3e54  CausalNonpurifiability/EC/Rectangles.lean
67abdf8bf921905ceb8cb40d3e97c65c1926fc9dba573584669b50f0ad04ed35  CausalNonpurifiability/EC/SOS.lean
e9cfd33cbda4fe94d06ae6c4cf4e5d783336e43e9374e8505e955710804de465  CausalNonpurifiability/Full.lean
c10088abcd02913c00031c97081300399c6993d6f735b61d5e4e4cb58fc00aee  CausalNonpurifiability/Linear/Indices.lean
8e6d9146b903e577c3e45f59ce322b2933acbb82948fcfd4c293eb3b26e5c554  CausalNonpurifiability/Linear/OpNorm.lean
c529ac9e87ae0ac5d80ced00a78081b0cb38fe7ee1a9e10f9c591c95acd75638  CausalNonpurifiability/Linear/OpNormDefinition.lean
70c61f428a5a52fcb7da228fac1a3409704612f31afc08a16bc4a57c1a9b5b33  CausalNonpurifiability/Linear/PartialTrace.lean
d0e6a489d3eb9a353705fe1da968e00652fdcd2d1e4b36001e671920c5638114  CausalNonpurifiability/Linear/Positive.lean
c2b2a6d422ef8a2c4e06d8874d58a9804b447ad4fc4281cc6e815a932e033dba  CausalNonpurifiability/Linear/Replacement.lean
7caee09874cd07b61eed0029f4ccf1b2c5a5b13cb48bea7f94333d58ed5e59a5  CausalNonpurifiability/Linear/Spectral.lean
c670a37aae40da9ad207bb436a30a2bb32ab00b86d087febb18139f39170a4f5  CausalNonpurifiability/Linear/Unitary.lean
5b181988dcdb5d8134ddbf0adc75fd4103ff0cef85110873bf27626f1a10eba3  CausalNonpurifiability/Main.lean
70594e038c0f403658913c55b9e66cef5740e68559aa38888741af3b82a276a2  CausalNonpurifiability/MainTheorem.lean
cc6bbcdd42188e43d399f9901249b1a1641f4da65d5000c9a9a227a88d75767a  CausalNonpurifiability/OCB.lean
949b925930f178565d418d0ddb955eaf78a14125a981a630017ff48c5e86c9fc  CausalNonpurifiability/OCBGame.lean
75a178eaec306dab7c95fce0c86e7f68ecc2b189c39abc70c91da58ee9b184dd  CausalNonpurifiability/Propositions.lean
445d9ede0ee7b9c2526ee5ae13b93d07d6a7727334413102a2ced452c3641306  CausalNonpurifiability/Purification/Family.lean
f01617b6a7d0782b28c3e5eca657403f5ba3437e36dd78c7eece108c8952883a  CausalNonpurifiability/Purification/Heisenberg.lean
88f57dfad072ec4d82b78f2f77497863897fbe76f0a2eb994577802f5858da03  CausalNonpurifiability/Purification/Necessity.lean
85fc3448d3710c6329772c2995df47d771fc80efe92b3af0ff9981e2e38a738e  CausalNonpurifiability/Purification/Sector.lean
d0a321578302d59aca1c473e84d225933a53f4e42b7e2032432ff768fc6d0e81  CausalNonpurifiability/Purification/Separation.lean
00ccacff6f704529b8295d89ce8c0b9c27ff5206c971e31de79a7f5e62e176ce  CausalNonpurifiability/Purification/Unitary.lean
cdf8e8180128de62353e3ae4126940905f02a9332e1e3d6e13cc5fb177c6a30a  CausalNonpurifiability/Robustness.lean
4448f5086866ce655235cf0218cda6aa64045d404212b8c28b45212e1a2a0430  CausalNonpurifiability/RobustnessEC.lean
6c30daf40c912aa23007a27a65e9732e6218b367a81b67dfa69ddde5d50614cb  CausalNonpurifiability/Statement.lean
6ef006f8f343eceaabcf9175e3c3a028e128323489380095af9c4a2c7a27aae9  CausalNonpurifiability/StatementCore.lean
53272faa9d58bf0391a18f448dd231bd0e6356d91ef265bd05ce523c426cba4e  CausalNonpurifiability/Unconditional.lean
db9737c6f91eb92794defcb613ec07f64558126e03d7f8f1b292cb8a3c8f39d0  CausalNonpurifiability/Uniform.lean
2a95299010d6e7a32b45919cdce92e6518fea8a994d00639d0d10e8a0ec20783  Challenge.lean
c0197db488ffa8e154edea20a26fa7a1c1c3e89675dfce43e72c16831966dd9b  Gemfile
d93caad3b41ab81138c1770dcde1415ac9aa47e8e469ea25b3f876a9f3d2cdff  Gemfile.lock
c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4  LICENSE
62ec4bfda5541919ce49ebc8ab6dc26362cc9050869103f4fbf60f86a05fc446  NOTICE
97608121a29500f7c78e9a2feb2c42382ecb958a1a5da245414e68b73edf012f  README.md
9fc3167593a06fc91d89ab7301cb0ce6bd3322d5a01eaccbbe50706fac303921  Solution.lean
211df3def90439664bce2fb05641a9c3191ed3a267d9882e809b28a474ab281d  comparator.json
6d57304e11fe63a61c07bc1943836304136ce724d64bb5b16a8df671c6e6757f  docs/FIDELITY.md
5bc7037a71a241e671ec1a89a8243e3f085526cf170f02937b2f1d8a0c74b154  docs/OQP_STATEMENT.md
2df068877b280c5da826c8f6c277a0049bdfb0067a250c88df587790a1f13196  formalization.yaml
1335f65b84e10aa7e66f07d6d313d3567ab677f436b361ac5684c6e8337a2f9d  lake-manifest.json
42ac2ad8594c695eb3384c11765be6c4ff8c10cb04e15cc7f29a22c9f8a0d102  lakefile.toml
8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7  lean-toolchain
27fabd506a355617be5d4708989fcd6dca161f03c4e1952234bd33daab23e890  paper/README.md
6919911f9905fcc9f01cac96e8c98a348a192a5550a10d127b0b3ced2d74bc5a  scripts/check-lean-sources.py
47eeb73febf48a2e23036e67f3223ea0562604139a7e97723c70cc4d5c269782  scripts/validate-formalization.rb
4fefa0e6c779448143b3164f56e96c3b6f719de67da335fa445127ab55f9b1e2  scripts/verify-comparator.sh
18801495c735d5ef93848b7ca045d44e71f11081e14a6ebed21159154d9177f8  test/validate_formalization_test.rb
```

## Logs kept in this repository

| File | SHA-256 |
|---|---|
| `verification/logs/check/build.log` | `6b51f83e59e769f32dea8878acb7a29ab6cb8dd582adc851611801f7b47deeac` |
| `verification/logs/check/axioms.log` | `6234c3d21959b4ad4fc23a753841880881d39be7df16497e66ae495a176e61c6` |
| `verification/logs/check/kernel-replay.log` | `5ee233e8d24f156e5946f89bae79c0c3deac50cb2b2fe384c6598aceaf0131a6` |
| `verification/logs/comparator/comparator.log` | `31eebcdcbd4c98a023666590333f32480fe9dc23041a4bad82044f4e28855bae` |

Commits after `3e78c71a3666` change only this file and `verification/logs/`; check with
`git diff --stat 3e78c71a3666 HEAD`.
