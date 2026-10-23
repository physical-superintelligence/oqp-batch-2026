# PPT composition bound: `2(d-1)` PPT maps compose to an entanglement-breaking map

This Lean development formalizes Theorem 1 of *Entanglement Breaking after 2(d-1) PPT Maps*. For every `d ≥ 2`, the composition of any `2(d-1)` PPT maps on `d × d` complex matrices is entanglement breaking. The maps may differ, and trace preservation is optional. The entanglement-breaking index of each PPT map is at most `2(d-1)`.

A PPT map is a complex-linear map that is completely positive and completely copositive. An entanglement-breaking map is completely positive and sends every positive bipartite operator to a separable operator when applied to one tensor factor.

Open Quantum Problem [38, *The PPT-squared conjecture*](https://oqp.iqoqi.oeaw.ac.at/the-ppt-squared-conjecture) concerns compositions of two PPT maps.

## Contents

- [Theorem statements](Challenge.lean) and [proofs](Solution.lean).
- [Definitions](PPTCompositionBound/Defs.lean) and [main argument](PPTCompositionBound/Main.lean).
- [Paper-to-formalization map](docs/FIDELITY.md) and [manuscript description](paper/README.md).
- [Problem statement](docs/OQP_STATEMENT.md).
- [Comparison configuration](comparator.json) and [axiom checks](PPTCompositionBound/Audit/FinalCheck.lean).
- [Metadata](formalization.yaml) and [historical verification receipts](verification/RECEIPTS.md).

## Main theorems

The declarations are in namespace `PPTCompositionBound`.

| Declaration | Statement |
| --- | --- |
| `compose_ppt_maps_entanglementBreaking` | For `d ≥ 2`, any `2(d-1)` PPT maps on `d × d` complex matrices compose to an entanglement-breaking map. |
| `ebIndex_le_of_isPPTMap` | For `d ≥ 2`, the entanglement-breaking index of a PPT map is at most `2(d-1)`. |
| `compose_at_least_ppt_maps_entanglementBreaking` | For `d ≥ 2`, any `N ≥ 2(d-1)` PPT maps compose to an entanglement-breaking map. |
| `compose_ppt_map_interleaved_entanglementBreaking` | For `d ≥ 2`, `2(d-1)` copies of a PPT map, interleaved with completely positive maps, compose to an entanglement-breaking map. |

`compList` applies the head of a list before the remaining maps. `ebIndex T` is the least integer `m ≥ 1` for which `T^m` is entanglement breaking, with value `⊤` when no such integer exists. Operators are unnormalized. The [statement map](docs/FIDELITY.md) describes the definitions and the additional theorems.

## Build and check

Run the commands from this directory, containing `lakefile.toml`. The same working directory applies when this folder is copied out as a standalone project.

The pins are Lean `leanprover/lean4:v4.35.0-rc4` in [lean-toolchain](lean-toolchain) and Mathlib `1b3c41969602424bd2f04b3d4f731734e5b00cde` in [lakefile.toml](lakefile.toml). The remaining dependency revisions are in [lake-manifest.json](lake-manifest.json). Use Git and elan; the comparison script also requires Linux, Python 3 and `bwrap`.

```sh
python3 scripts/check-lean-sources.py
lake exe cache get
lake build
./scripts/verify-comparator.sh
```

`Challenge.lean` contains the theorem statements with deliberate proof placeholders. `Solution.lean` supplies their proofs. The comparison configuration selects thirteen declarations. The axiom-check module specifies `propext`, `Classical.choice` and `Quot.sound` for those declarations.

The [verification receipts](verification/RECEIPTS.md) identify the historical checks by date and file hash.

## Proof outline

A pair of PPT maps lowers the Schmidt number of a positive input by one, down to one. Iterating over `d-1` pairs gives a separable output. The [paper-to-formalization map](docs/FIDELITY.md) connects the argument to the definitions and declarations.

## Citation

See [CITATION.cff](CITATION.cff).

## License

Apache License 2.0: [LICENSE](LICENSE) and [NOTICE](NOTICE).
