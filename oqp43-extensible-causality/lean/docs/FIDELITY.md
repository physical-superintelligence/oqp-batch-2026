# Fidelity: the text of Open Quantum Problem 43 and the Lean statements

This file maps each part of the problem statement ([`OQP_STATEMENT.md`](OQP_STATEMENT.md)) to the
Lean definitions and theorems in [`Challenge.lean`](../Challenge.lean). All definitions named
below are in the namespace `CausalNonpurifiability`; all theorems in
`CausalNonpurifiability.OQP43`. The definitions in `Challenge.lean` are verbatim copies of the
library's, so the library proves statements about exactly these objects.

## 1. The question and the answer

| Problem text | Lean |
|---|---|
| "The question is whether or not any extensibly causal process is purifiable." | `not_all_extensiblyCausal_purifiable : ∃ W : PMat qubits, ExtensiblyCausal qubits W ∧ ¬ Purifiable qubits W` |
| (the witness) | `theorem_1_1`: the explicit four-qubit process `Wq` is a process matrix, positive definite, extensibly causal, not causally separable, and not purifiable; `wq_pauli_form` gives its Pauli form `(20 IIII + 10 ZIII + 10 IIZI + 5 ZIZI + 4 IZZI + 4 ZIXZ)/80` |
| (all dimensions, two parties) | `dimension_dichotomy`: for port dimensions `D = (m, d, n, e)`, every extensibly causal process is purifiable if and only if `min(m, d, n, e) = 1` |

The answer proved is **no**: some extensibly causal process is not purifiable.

## 2. Process matrices

| Problem text | Lean |
|---|---|
| "$W \in A^1_I \otimes A^1_O \otimes ... \otimes A^N_I \otimes A^N_O$ is a process matrix with $A^i_I$ and $A^i_O$ being the input and the output Hilbert spaces of party $i$" | `Ports` (the four dimensions `m = dim A_I`, `d = dim A_O`, `n = dim B_I`, `e = dim B_O`, all positive), `PMat D` (complex matrices indexed by `((a_I, a_O), (b_I, b_O))`); `N = 2` |
| "The set of process matrices is defined by requiring that probabilities are well-defined [1,2]." | `Valid D W`: `W` Hermitian, the three linear conditions `GenLV` (written with the replacement maps `R_AO`, `R_BO`, `R_BIBO`, `R_AIAO`), `W ≥ 0` and `Tr W = d e`. Theorem `valid_iff_channels_normalized`: for positive `W` these conditions hold exactly when every pair of local channels gives total probability `Tr[W (M ⊗ N)] = 1` |
| "$p = \mbox{Tr}[(M_{a_1|x_1} \otimes ... \otimes M_{a_N|x_N}) W]$", "CJ representations of the CP maps" | `Instrument`: the transposed Choi matrices `M_{a|x} = J(𝒜_{a|x})ᵀ ≥ 0` on input ⊗ output with `Tr_O ∑_a M_{a|x} = 1`; `bornExtended` is `Re Tr[(W ⊗ σ)(M_{a|x} ⊗ N_{b|y})]` |

## 3. Causal and extensibly causal processes

| Problem text | Lean |
|---|---|
| "decomposed into a convex combination of a probability distribution which is no-signaling from Bob to Alice ($p^{A<B}$) and a probability distribution which is no-signaling from Alice to Bob ($p^{B<A}$): $p_{causal} = \lambda p^{A<B} + (1 - \lambda) p^{B<A}$" | `Causal p`: there are `λ ∈ [0, 1]` and probability tables `pAB`, `pBA` (`Conditional`) with `NS_AB pAB`, `NS_BA pBA` and `p = λ pAB + (1 - λ) pBA` for all settings and outcomes, one `λ` for all settings |
| "they are called *extensibly causal* if they remain causal even under extension with input systems in an arbitrary joint quantum state [3]" | `ExtensiblyCausal D W`: `Valid D W`, and for all ancilla dimensions `r + 1`, `s + 1`, every density operator `σ` on `R_A ⊗ R_B` (entangled states included), all finite numbers of settings and outcomes, and every pair of instruments on the extended inputs `A_I ⊗ R_A`, `B_I ⊗ R_B`, the distribution `bornExtended D W σ M N` is `Causal` |

## 4. Pure and purifiable processes

| Problem text | Lean |
|---|---|
| "after extending them with a global past state from the Hilbert space $P$ and a global future state from the Hilbert space $F$" | `HigherOp D p f`: operators on `P ⊗ (A_I ⊗ A_O ⊗ B_I ⊗ B_O) ⊗ F` with `dim P = p + 1`, `dim F = f + 1` |
| "they induce a unitary transformation from the past to the future whenever unitary transformations are also applied in the local laboratories [5]" | `Pure D S`: `S` is `Deterministic` (positive, and channels of the two parties are mapped by the link product `link` to a channel from the past to the future) and every pair of unitary channels (`UnitaryChoi`, both `Uᴴ U = 1` and `U Uᴴ = 1`) is mapped to a unitary channel, for additional systems of every finite dimension |
| "purifiable if one can recover it from a pure process $S$ ... by inputing the state $\lvert 0\rangle$ in $P'$ and tracing out the state from $F'$: $W=\mbox{Tr}_{P'F'} [S^T (\lvert 0\rangle \langle 0\rvert^{P'} \otimes \mathbb{I}^{F'})]$" | `Purifiable D W`: `∃ p f S, Pure D S ∧ reducePastFuture D S = W`, where `reducePastFuture D S = Tr_F [⟨0|_P S |0⟩_P]` |
| "$S^T$ is transposed process $S$" | `purifiable_iff_transpose_formula`: `Purifiable D W ↔ ∃ p f S, Pure D S ∧ (reducePastFuture D S)ᵀ = W`, so the definition with `S` and the problem's formula with the full transpose `S^T` give the same purifiable processes |
| (which processes are purifiable) | `ordered_processes_purifiable`: causally ordered processes are purifiable; `purifiable_causallySeparable`: purifiable processes are causally separable |

## 5. Conventions

1. **Two parties.** Processes are operators `W` on `A_I ⊗ A_O ⊗ B_I ⊗ B_O` for two parties, Alice
   and Bob. The purifying spaces `P'` and `F'` of the problem are the past and future of `S` in
   `Purifiable`.
2. **Finite dimensions.** All spaces are finite-dimensional. The laboratory dimensions are the
   four positive numbers of `Ports`; ancilla dimensions, numbers of settings and outcomes, and the
   dimensions of `P'`, `F'` and of the additional systems are written `k + 1` (types
   `Fin (k + 1)`), which ranges over all positive finite dimensions and all nonempty finite
   alphabets. In particular `theorem_1_1` excludes purifications with `P'`, `F'` of every finite
   dimension.
3. **Purity.** As in Definitions 1 and 3 of Araújo, Feix, Navascués and Brukner (reference [5] of
   the problem), the local unitaries may act on additional input and output systems of any finite
   dimension. A unitary channel satisfies both `Uᴴ U = 1` and `U Uᴴ = 1`.
4. **Born rule.** `bornExtended` is `Re Tr[(W ⊗ σ)(M_{a|x} ⊗ N_{b|y})]`; for positive `W` and `σ`
   the trace is real (library theorem `bornExtended_im_zero`).
5. **Choi convention.** As in the paper, for a completely positive map `𝒜` the Choi matrix is
   `J(𝒜) = ∑_{i,j} |i⟩⟨j| ⊗ 𝒜(|i⟩⟨j|)`. Instrument elements are the transposes `M = J(𝒜)ᵀ` (the
   "CJ representations" of the problem, as in its reference [1]), so the Born rule is
   `Tr[W (M ⊗ N)]`. The definition of purity uses the untransposed `J` (`ChannelChoi`,
   `UnitaryChoi`, `link`), and the link product carries the partial transpose on the laboratory
   factors, as in Eq. (1) of Araújo, Feix, Navascués and Brukner. The problem's formula with `S^T`
   and the definition with `reducePastFuture` give the same purifiable processes
   (`purifiable_iff_transpose_formula`).
6. **The witness.** `Wq` is defined as the case `m = d = n = e = 2` of a rational construction
   `W0 m d n e`, mapped entrywise into the complex numbers; `wq_pauli_form` states that it equals
   the Pauli sum of the paper.
7. **The defined notions on examples.** `white_process_purifiable` (the white-noise process
   `I/(mn)`, in which each party receives the maximally mixed state, is a process matrix and is
   purifiable, in every dimension) and `theorem_1_1` give a purifiable process and one that is not
   purifiable; `theorem_1_1` and `ocb_process_not_extensiblyCausal` (the process of Oreshkov, Costa
   and Brukner is a process matrix that is not extensibly causal) give an extensibly causal process
   and one that is not; `swap_table_not_causal` gives a distribution that is not causal.
   `ordered_processes_purifiable` (every causally ordered process is purifiable, in every
   dimension, signalling ones included) and `purifiable_causallySeparable` place `Purifiable`
   between the causally ordered and the causally separable processes, and the "if" direction of
   `dimension_dichotomy` makes every extensibly causal process purifiable when one dimension is
   `1`.
8. **Hypotheses.** The statements carry exactly the hypotheses displayed in them. No axioms are
   declared, and the theorem used to exclude purifications (purifiable processes are causally
   separable; Yokojima, Quintino, Soeda and Murao, Corollary 1; Barrett, Lorenz and Oreshkov,
   Theorem 3) is proved in the library and stated as `purifiable_causallySeparable`.
