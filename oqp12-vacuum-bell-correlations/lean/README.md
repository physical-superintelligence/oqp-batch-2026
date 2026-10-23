# Bell inequalities for long range vacuum correlations (Open Quantum Problem 12) in Lean

This repository contains a Lean 4 proof about the vacuum of the massive real free scalar field in
3+1-dimensional Minkowski space: for every mass `m > 0` and any two bounded regions, once the second
region is moved far enough along a fixed spacelike direction, or by a spatial translation of length at
least a threshold that is the same for all directions, every choice of local observables satisfies the
**CHSH inequality** in the vacuum. This answers Problem 12 of the IQOQI Vienna Open Quantum Problems,
"Decide whether some (necessarily small) violation of the inequalities is possible for regions
arbitrarily far apart" ([problem statement](docs/OQP_STATEMENT.md)), in the negative for bounded regions moved apart in
these two ways. The repository also proves Theorem 1.1 and Corollary 1.2 of the paper *The vacuum Bell correlation of the massive free scalar field attains the classical bound for bounded regions beyond a finite separation*
in its full-manuscript version of 21 October 2026 (see [manuscript correspondence](paper/README.md)), and the existence of
the vacuum representation for every mass `m > 0`. The theorem and equation numbers below follow
that full manuscript. The letter of 22 October 2026 presents the main results as Theorem 1 and
Corollary 1.

## The theorems

[`Challenge.lean`](Challenge.lean) contains the formal statements. It imports only Mathlib and contains six theorems, in the
namespace `VacuumBellSeparation.OQP12`; [`Solution.lean`](Solution.lean) proves them from the library
`VacuumBellSeparation/`. The headline:

```lean
theorem no_chsh_violation_far_apart (m : ℝ) (hm : 0 < m)
    (O₁ O₂ : Set Spacetime) (hO₁ : Bornology.IsBounded O₁) (hO₂ : Bornology.IsBounded O₂)
    (a : Spacetime) (ha : a.1 ^ 2 < ‖a.2‖ ^ 2) :
    ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (V : FreeFieldVacuum m H) (A₀ A₁ B₀ B₁ : H →L[ℂ] H),
        A₀ ∈ localAlgebra V O₁ → A₁ ∈ localAlgebra V O₁ →
        B₀ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) →
        B₁ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) →
        IsSelfAdjoint A₀ → IsSelfAdjoint A₁ → IsSelfAdjoint B₀ → IsSelfAdjoint B₁ →
        ‖A₀‖ ≤ 1 → ‖A₁‖ ≤ 1 → ‖B₀‖ ≤ 1 → ‖B₁‖ ≤ 1 →
        ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖ ≤ 2
```

In words: for every mass `m > 0`, any two bounded regions `O₁, O₂` and any spacelike vector `a`, there is
a `T₀` (depending on `m`, `O₁`, `O₂` and `a`) such that, once the second region is translated by `t a`
with `t ≥ T₀`, every choice of observables (self-adjoint operators of norm at most 1) localized in the two
regions satisfies `|⟨Ω, (A₀(B₀ + B₁) + A₁(B₀ − B₁)) Ω⟩| ≤ 2` in the vacuum `Ω`. This is Corollary 1.2 of
the paper, stated in CHSH form. The second CHSH theorem:

```lean
theorem no_chsh_violation_far_apart_uniform (m : ℝ) (hm : 0 < m)
    (O₁ O₂ : Set Spacetime) (hO₁ : Bornology.IsBounded O₁) (hO₂ : Bornology.IsBounded O₂) :
    ∃ D : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), D ≤ ‖x‖ →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (V : FreeFieldVacuum m H) (A₀ A₁ B₀ B₁ : H →L[ℂ] H),
        A₀ ∈ localAlgebra V O₁ → A₁ ∈ localAlgebra V O₁ →
        B₀ ∈ localAlgebra V ((fun y => y + ((0 : ℝ), x)) '' O₂) →
        B₁ ∈ localAlgebra V ((fun y => y + ((0 : ℝ), x)) '' O₂) →
        IsSelfAdjoint A₀ → IsSelfAdjoint A₁ → IsSelfAdjoint B₀ → IsSelfAdjoint B₁ →
        ‖A₀‖ ≤ 1 → ‖A₁‖ ≤ 1 → ‖B₀‖ ≤ 1 → ‖B₁‖ ≤ 1 →
        ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖ ≤ 2
```

| Theorem | Content |
|---|---|
| `no_chsh_violation_far_apart` | the headline above |
| `no_chsh_violation_far_apart_uniform` | one distance `D` for two bounded regions such that the CHSH inequality holds whenever the second region is moved by any spatial vector of length at least `D`, in any direction |
| `theorem_1_1` | Theorem 1.1 of the paper: there is `C_* > 2` such that for all `m, R > 0` and `L ≥ C_* R`, the vacuum Bell correlation `β_m(R, L)` of the double cones `D_R` and `D_R + (0, L𝐞₁)` (radius `R`, centres at spatial distance `L`) equals `1` |
| `corollary_1_2` | Corollary 1.2 of the paper: for fixed bounded regions and a fixed spacelike direction, the vacuum Bell correlation equals `1` for all large translations |
| `freeFieldVacuum_exists` | a vacuum Weyl system exists for every mass `m > 0` |
| `localAlgebra_open_nonabelian` | sanity check: the local algebra of every nonempty open region contains two operators that do not commute |

Each of the six theorems depends exactly on the axioms `propext`, `Classical.choice` and `Quot.sound`.
Comparator checks that the theorems proved in `Solution.lean` are exactly the statements of
`Challenge.lean`, with these three axioms permitted.

Reading the statements:

- `Spacetime` is `ℝ × ℝ³`, points `(x⁰, 𝐱)`. A vector `a` is spacelike when `(a⁰)² < ‖𝐚‖²`.
- `FreeFieldVacuum m H` is a vacuum Weyl system of the free field of mass `m`: unitary Weyl operators
  `W(F) = e^{iφ(F)}` indexed by real smooth compactly supported test functions on spacetime, satisfying the
  Weyl relations of the one-particle inner product with measure `d³p / (2(2π)³ ω_m(𝐩))`, together with a
  cyclic unit vector `Ω` with `⟨Ω, W(F) Ω⟩ = exp(−‖κ_m F‖²/2)`. These data fix the vacuum representation
  up to unitary equivalence (the library proves this, and builds the representation on the symmetric Fock
  space). Every theorem holds for all such systems.
- `localAlgebra V O` is the von Neumann algebra generated by the Weyl operators of test functions supported
  in `O`.
- In `theorem_1_1` and `corollary_1_2` the Summers–Werner Bell correlation of the vacuum is written out as
  the supremum of the CHSH values `½ |⟨Ω, (A₀(B₀ + B₁) + A₁(B₀ − B₁)) Ω⟩|` over observables of the two
  regions; its classical bound is `1` (a CHSH value of `2`) and, for commuting algebras such as those of
  spacelike separated regions, Tsirelson's bound is `√2`, so `β = 1` means
  that every choice of local observables satisfies the CHSH inequality.

[Definitions and problem correspondence](docs/FIDELITY.md) maps the problem text and the full manuscript's results to these Lean definitions and theorems.

## How to check

Build requirements: Linux or macOS, [elan](https://github.com/leanprover/elan), Git, and Python 3.
The Comparator script additionally requires Linux with `bubblewrap`. Run the commands below from this directory, which contains
[`lakefile.toml`](lakefile.toml). The toolchain is pinned in [`lean-toolchain`](lean-toolchain)
(Lean v4.35.0-rc4) and Mathlib in [`lake-manifest.json`](lake-manifest.json)
(commit `1b3c41969602424bd2f04b3d4f731734e5b00cde`).

```text
python3 scripts/check-lean-sources.py         # module headers and file sizes
python3 scripts/check-challenge-definitions.py # Challenge definitions equal the library text; "1 verbatim blocks checked"
lake exe cache get                             # prebuilt Mathlib
lake build                                     # library, axiom check, Challenge and Solution
./scripts/verify-comparator.sh                 # Comparator (Lean kernel, NanoDa, con-ron); ends "Your solution is okay!"
```

`lake build` ends with `Build completed successfully` and reports the six `sorry` placeholders of
`Challenge.lean` as warnings (they mark the formal statements). The build includes
`VacuumBellSeparation/Audit/FinalCheck.lean`, which fails it unless `#print axioms` reports exactly
`propext`, `Classical.choice` and `Quot.sound` for each theorem in `comparator.json`.

The [verification receipts](verification/RECEIPTS.md) record these commands running on
21 October 2026 at source commit `6a91bb4b256579eb39f6a5f08f2cb0c1e9bc94e5`, on a
fresh Ubuntu 24.04 machine with 32 cores and 128 GiB of memory.

Resources: the library has 1,015 Lean files (about 105,800 lines). The recorded release checks
([verification receipts](verification/RECEIPTS.md)) ran on 16-core Linux machines with 128 GiB of memory: the fresh build, axiom
audit and kernel replay of the theorems' dependency closure took 1,368 s (about 23 minutes), and
`lake comparator --paranoid` with the Lean kernel and the independent kernels lean4lean, NanoDa, con-leche
and con-ron 2,902 s (about 48 minutes). The CI workflow (`.github/workflows/ci.yml`) runs `lake build` and
`./scripts/verify-comparator.sh` (not the `--paranoid` run); give it a runner with 16 or more cores.

## Proof outline

The paper's argument, as formalized:

| Paper | Lean |
|---|---|
| Definitions of Section 2.1 (Weyl system, local algebras, Bell correlation (2.4)) | `Bell/Defs.lean`, `FreeField/Defs.lean` |
| Lemma 2.1 (dilation) | `FreeField/Dilation.lean`, `lemma_2_1` |
| Theorem 3.1 (two event bounds and clustering give `β = 1`) | `Bell/Theorem31.lean`, `probability_criterion` |
| Sections 4–8 (thermal comparison, Gaussian estimates, Bessel bounds, polynomial selectors, regional estimates (8.11), (8.13)) | `Gaussian/`, `Special/BesselK.lean`, `Polynomial/Selector.lean`, `FreeField/Section8EstimatesProof.lean` |
| Microcausality of the free field | `FreeField/Microcausality/` |
| Section 8.4, proof of Theorem 1.1 | `FreeField/MainReduction.lean`, `FreeField/Main.lean`, `FreeField/MainTheorems.lean` |
| Proof of Corollary 1.2 (Lorentz covariance, isotony, `β ≥ 1`) | `FreeField/Corollary.lean`, `FreeField/Lorentz.lean`, `FreeField/Isotony.lean` |
| Existence of the vacuum representation | `FreeField/Existence.lean`, `Weyl/Existence.lean` |
| CHSH form of the results, uniform version, written-out Theorem 1.1 and Corollary 1.2 | `FreeField/OQP12.lean` |

Paths are relative to `VacuumBellSeparation/`. The library contains no `sorry` and no `axiom`.
[docs/PAPER_TO_LEAN.md](docs/PAPER_TO_LEAN.md) maps every numbered statement, equation and table of the paper to its Lean counterpart, where there is one.

## Paper

*The vacuum Bell correlation of the massive free scalar field attains the classical bound for bounded regions beyond a finite separation*, full manuscript of 21 October 2026. See [manuscript correspondence](paper/README.md).

## Citation

See [CITATION.cff](CITATION.cff), including its full-manuscript reference.

## License

Apache License 2.0 ([LICENSE](LICENSE)); see [NOTICE](NOTICE). Mathlib and the Lean toolchain keep their own licenses.
