# Extensibly causal processes that are not purifiable (Open Quantum Problem 43)

Lean 4 proves that not every extensibly causal process is purifiable: a negative answer to Problem
43 of the IQOQI Vienna list of Open Quantum Problems, *Are all extensibly causal processes
purifiable?*. The witness is the process
matrix `W_q = (20 IIII + 10 ZIII + 10 IIZI + 5 ZIZI + 4 IZZI + 4 ZIXZ)/80` on
`A_I ⊗ A_O ⊗ B_I ⊗ B_O` for two parties, Alice and Bob, whose input and output systems are qubits
(`X` and `Z` are Pauli matrices). `W_q` is a process matrix of full rank; it is extensibly causal
(its correlations are causal for every ancilla state that Alice and Bob may share, entangled states
included, of every finite dimension, and for all local instruments) and causally nonseparable; and
it is not purifiable: no pure process, in the sense of Araújo, Feix, Navascués and Brukner, with
past and future spaces of any finite dimension, yields `W_q` when the state `|0⟩` is input in its
past and its future is traced out. The problem's text is in
[`docs/OQP_STATEMENT.md`](docs/OQP_STATEMENT.md), and [`docs/FIDELITY.md`](docs/FIDELITY.md) maps
its wording to the Lean definitions.

The accompanying paper is *An extensibly causal quantum process with no
purification*. The [paper map](paper/README.md) connects the current paper's
process `S` and dimension dichotomy to the Lean declarations.

## Contents

- [Theorem statements](Challenge.lean) and [proofs](Solution.lean)
- [Proof library](CausalNonpurifiability/)
- [Paper map](paper/README.md) and [problem definition map](docs/FIDELITY.md)
- [Metadata](formalization.yaml), [comparison configuration](comparator.json),
  and [historical verification receipts](verification/RECEIPTS.md)

## The theorems

From [`Challenge.lean`](Challenge.lean), namespace `CausalNonpurifiability.OQP43`:

```lean
theorem not_all_extensiblyCausal_purifiable :
    ∃ W : PMat qubits, ExtensiblyCausal qubits W ∧ ¬ Purifiable qubits W

theorem theorem_1_1 :
    Valid qubits Wq ∧ Wq.PosDef ∧ ExtensiblyCausal qubits Wq ∧ ¬ CausallySeparable qubits Wq ∧
      ¬ Purifiable qubits Wq
```

Axioms: `propext`, `Classical.choice` and `Quot.sound`, for these and for the nine theorems below.

| Theorem | Content |
|---|---|
| `wq_pauli_form` | `W_q` is the Pauli sum above |
| `dimension_dichotomy` | for two parties with positive finite port dimensions `(m, d, n, e)`: every extensibly causal process is purifiable if and only if `min(m, d, n, e) = 1` |
| `purifiable_causallySeparable` | every purifiable process matrix is causally separable (Yokojima, Quintino, Soeda and Murao, Corollary 1; Barrett, Lorenz and Oreshkov, Theorem 3; Theorem 6.1 of the paper) |
| `ordered_processes_purifiable` | every process matrix in which Alice acts before Bob, or Bob before Alice, is purifiable, in all dimensions (Araújo, Feix, Navascués and Brukner, Section 3; Proposition 9.2 of the paper) |
| `purifiable_iff_transpose_formula` | the problem's recovery formula `W = Tr_{P'F'}[S^T (\|0⟩⟨0\|^{P'} ⊗ I^{F'})]`, with the transposed `S^T`, defines the same purifiable processes as `Purifiable` |
| `valid_iff_channels_normalized` | for positive `W`: `W` is a process matrix exactly when every pair of local channels gives total probability 1 (the problem's "probabilities are well-defined") |
| `white_process_purifiable` | the white-noise process `I/(mn)`, in which each party receives the maximally mixed state, is a process matrix, ordered both ways, and purifiable, in all dimensions |
| `swap_table_not_causal` | the two-way signalling distribution `[a = y][b = x]` on bits is not causal |
| `ocb_process_not_extensiblyCausal` | the process `W_OCB` of Oreshkov, Costa and Brukner is a process matrix that is not extensibly causal |

`Challenge.lean` imports only Mathlib and contains every definition the statements use, copied
verbatim from the library, so the statements can be read without the proofs.
[`Solution.lean`](Solution.lean) proves them from the library, and
[`comparator.json`](comparator.json) lists the eleven theorems and the three permitted axioms.

## How to check

Requirements: Linux or macOS with [`elan`](https://github.com/leanprover/elan), Git and Python 3;
for Comparator also Linux with `bwrap` (bubblewrap). Run the commands from the
directory containing this README, including when the formalization folder is
copied out on its own. The toolchain is pinned in
[`lean-toolchain`](lean-toolchain) to `leanprover/lean4:v4.35.0-rc4`.
[`lakefile.toml`](lakefile.toml) and [`lake-manifest.json`](lake-manifest.json)
pin Mathlib to `1b3c41969602424bd2f04b3d4f731734e5b00cde`.

```text
lake exe cache get                     # download compiled Mathlib (several GiB)
python3 scripts/check-lean-sources.py  # module headers and file sizes; prints nothing on success
lake build                             # library, axiom pin, Challenge and Solution
./scripts/verify-comparator.sh         # Comparator with Lean's kernel, NanoDa and con-ron
```

The build targets are the proof library, its axiom audit, `Challenge` and
`Solution`. A successful `lake build` ends with `Build completed successfully`, with one
`` declaration uses `sorry` `` warning for each of the eleven statements in `Challenge.lean` (the
placeholders whose proofs are in `Solution.lean`) and linter and deprecation warnings from the
library. It also builds `CausalNonpurifiability/Audit/FinalCheck.lean`, which stops the build
unless each of the eleven theorems depends on exactly the axioms `propext`, `Classical.choice` and
`Quot.sound`.
A successful `verify-comparator.sh` run ends with `Your solution is okay!`.
The [historical verification receipts](verification/RECEIPTS.md) identify the
checked commit `3e78c71a3666e793b8bc1efb19113873c652a9a1` and the checks run on
14 October 2026, with file hashes and logs.

## Proof outline

| Paper | Lean (library) | File |
|---|---|---|
| `W_q` is a process matrix of full rank | `wq_valid`, `w0_qubit_posDef` | `Certificates/Qubit.lean` |
| `W_q` is causally nonseparable: a causal witness `S_0` with `Tr(S_0 W_q) < 0` | `witness_nonneg_on_cs`, `wq_not_causallySeparable` | `Certificates/Witness.lean` |
| `W_q` is extensibly causal: rectangle bounds from a signed decomposition and an operator sum of squares (Lemma 5.2), then a transport argument that assembles a causal decomposition | `rectangles_qubits`, `operator_sos_two`, `transport_of_rectangles`, `ec_of_rectangles`, `wq_extensiblyCausal` | `EC/Rectangles.lean`, `EC/SOS.lean`, `Classical/Transport.lean`, `EC/Bridge.lean`, `Main.lean` |
| Theorem 6.1: purifiable processes are causally separable | `purifiable_causallySeparable` | `Purification/Necessity.lean` |
| Proposition 9.2: causally ordered processes are purifiable | `ordered_purifiable` | `Boundary/Dilation.lean` |
| Theorem 1.1 | `theorem_intro`, `eq_qubit_pauli` | `MainTheorem.lean` |
| The answer to Problem 43 | `oqp43_negative` | `Unconditional.lean` |
| The dichotomy: the construction in all dimensions at least 2; if a dimension is 1, every process is causally ordered and purifiable | `uniform_kernel`, `one_dimensional_purifiable`, `dimension_dichotomy` | `Full.lean`, `Boundary/Dilation.lean`, `Unconditional.lean` |
| The transposed recovery formula (Appendix B) | `purifiable_iff_transpose_convention` | `Boundary/Transpose.lean` |
| Lemma 2.3 | `valid_iff_channel_normalization` | `Definitions/Channels.lean` |
| `W_OCB` violates a causal inequality (Appendix C) | `appC_OCB_game` | `OCBGame.lean` |

File paths are relative to `CausalNonpurifiability/`; theorem numbering in this
outline follows the October 2026 source draft *Extensible causality without
purification*. The [paper map](paper/README.md) identifies the corresponding
statements in the accompanying paper.

## Citation and paper

Use [`CITATION.cff`](CITATION.cff) to cite the formalization.
The [paper map](paper/README.md) describes the accompanying paper and the source
draft used for the formalization's theorem numbering.

## License

Apache License 2.0 ([`LICENSE`](LICENSE), [`NOTICE`](NOTICE)). The quoted problem statement in
`docs/OQP_STATEMENT.md` is the IQOQI Vienna Open Quantum Problems text, quoted with attribution.
