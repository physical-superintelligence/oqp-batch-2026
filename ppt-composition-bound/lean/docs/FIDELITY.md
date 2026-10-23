# Statement fidelity

This note maps the wording of the paper and of Problem 38 of the Open Quantum Problems list
([OQP_STATEMENT.md](OQP_STATEMENT.md)) to the Lean definitions and theorems in
[`Challenge.lean`](../Challenge.lean).

## 1. What is proved

For every `d ≥ 2` and any PPT maps `Φ_1, …, Φ_{2(d-1)}` on `M_d = Matrix (Fin d) (Fin d) ℂ`, the
composition `Φ_{2(d-1)} ∘ ⋯ ∘ Φ_1` is entanglement breaking
(`PPTCompositionBound.compose_ppt_maps_entanglementBreaking`). The maps may all be different, trace
preserving or not. Consequences proved alongside: the entanglement-breaking index of a PPT map on
`M_d` is at most `2(d-1)` (`ebIndex_le_of_isPPTMap`); compositions of any `N ≥ 2(d-1)` PPT maps are
entanglement breaking (`compose_at_least_ppt_maps_entanglementBreaking`); and `2(d-1)` copies of one
PPT map with arbitrary completely positive maps between them compose to an entanglement-breaking map
(`compose_ppt_map_interleaved_entanglementBreaking`).

The hypotheses are exactly those in the statements: `2 ≤ d`, the PPT (or complete positivity)
assumptions on the maps, and `N ≥ 2(d-1)` for longer compositions. The proofs use the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## 2. The paper

The formalized manuscript is *Entanglement Breaking after 2(d-1) PPT Maps* (October 2026
draft; see [paper/README.md](../paper/README.md)).

- **Theorem 1** (first sentence) is `compose_ppt_maps_entanglementBreaking`, with the paper's
  generality: the maps may differ, trace preserving or not.
- **Theorem 1** (second sentence, the index) is `ebIndex_le_of_isPPTMap`. The index `ebIndex T` is
  the least `m ≥ 1` such that `T^m` is entanglement breaking, and `⊤` if there is none
  (`zero_map_isPPTMap_and_ebIndex_eq_one`, `ebIndex_id_eq_top`).
- **PPT maps.** A PPT map is completely positive and completely copositive (`IsPPTMap`), as in the
  paper's abstract. Both conditions are part of the definition: transposition on `M_2` is completely
  copositive and not completely positive
  (`transposeMap_isCompletelyCopositive_not_isCompletelyPositive`).
- **Order of composition.** `compList [Φ_1, …, Φ_N] = Φ_N ∘ ⋯ ∘ Φ_1`: the head of the list acts
  first (`compList_pair`). Any order works for the main theorem, since every map in the list is PPT.
  Lean counts from `0`, so the paper's `Φ_i` is `Φ (i - 1)`.
- **Number of maps and extensions.** Theorem 1 concerns exactly `2(d-1)` maps;
  `compose_at_least_ppt_maps_entanglementBreaking` covers any `N ≥ 2(d-1)`, and
  `compose_ppt_map_interleaved_entanglementBreaking` the interleaved form.
- **The proof:** a pair of PPT maps lowers the Schmidt number of a positive input by one, down
  to one. Iteration over `d-1` pairs gives a separable output. The library includes block positivity
  with a pseudo-inverse, equal-diagonal-block separability and a Schmidt-number lifting lemma.

## 3. Problem 38, phrase by phrase

Problem 38 asks whether **two** PPT states always swap to a separable state; in map form, whether any
two PPT maps compose to an entanglement-breaking map. The table maps each phrase of the entry to its
counterpart in this repository (the entry's LaTeX is rendered as plain text; the exact text is in
[OQP_STATEMENT.md](OQP_STATEMENT.md)).

| Problem 38 says | Counterpart here |
|---|---|
| "quantum states with positive partial transpose (i.e., they are “PPT-states”)" `ρ_AB`, `ρ_CD` | PPT maps (`IsPPTMap`: completely positive and completely copositive), through their Choi matrices: `choi_isPPTMap_iff` proves that a map is PPT exactly when its Choi matrix `(id_d ⊗ Φ)(\|Ω⟩⟨Ω\|)` is positive and has positive partial transpose (`partialTransposeRef`). |
| "let `M` be a positive operator decribing [sic] a yes/no measurement on the BC-system" | A completely positive map between the two PPT maps. `compose_ppt_map_interleaved_entanglementBreaking` allows arbitrary completely positive maps between copies of one PPT map `T`, and a PPT map preceded by a completely positive map is again PPT (the library lemma `IsPPTMap.comp_isCompletelyPositive`). |
| "`σ_AD = λ tr_BC((ρ_AB ⊗ ρ_CD)(1_A ⊗ M ⊗ 1_D))`" (entanglement swapping) | In map form, the swapped state corresponds, up to normalization and transposition conventions, to the Choi matrix of the composed map; `choi_isEntanglementBreaking_iff` relates entanglement breaking to separability of the Choi matrix. |
| "`λ` is a normalization factor" | All notions here are cones: operators are unnormalized and maps are arbitrary linear maps; separability and entanglement breaking are unchanged by positive scaling. |
| "`σ_AD` ... separable" | `IsSeparable X`: `X` is a finite sum of Kronecker products `A_i ⊗ B_i` of positive semidefinite matrices (the empty sum gives `0`). Entanglement breaking (`IsEntanglementBreaking`): completely positive, and `(id_k ⊗ Φ)(X)` is separable for every `k` and every positive `X`. `choi_isEntanglementBreaking_iff` proves the criterion: entanglement breaking exactly when the Choi matrix is separable. |
| "all such `σ_AD` are separable" | `compose_ppt_maps_entanglementBreaking`: on `M_d`, any **`2(d-1)`** PPT maps compose to an entanglement-breaking map. |

## 4. Conventions

- `M_d` is `Matrix (Fin d) (Fin d) ℂ`. A map is a `ℂ`-linear map between matrix algebras; the main
  theorem uses endomorphisms `Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)`.
- An operator on `ℂ^k ⊗ ℂ^d` is a `Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ`, reference factor first;
  `refMap (Fin k) Φ` is `id_k ⊗ Φ`, applying `Φ` to every block.
- "Positive" is `Matrix.PosSemidef` (Hermitian with nonnegative quadratic form).
- Complete positivity quantifies over every finite reference dimension `k`. Complete copositivity is
  complete positivity of `t ∘ Φ`, where `t` transposes the output.
- "PPT map" means completely positive and completely copositive.
- `pureState v = v v*`, and `partialTransposeRef` swaps the reference block indices.
- The sanity theorems check the definitions: some positive operator on `ℂ² ⊗ ℂ^d` is not separable
  (`exists_posSemidef_not_isSeparable`); the identity map is not entanglement breaking
  (`id_not_entanglementBreaking`); the three Choi criteria hold (`choi_isCompletelyPositive_iff`,
  `choi_isPPTMap_iff`, `choi_isEntanglementBreaking_iff`); complete copositivity does not imply
  complete positivity (`transposeMap_isCompletelyCopositive_not_isCompletelyPositive`); and the
  conventions of `compList` and `ebIndex` are as stated (`compList_pair`,
  `zero_map_isPPTMap_and_ebIndex_eq_one`, `ebIndex_id_eq_top`).
