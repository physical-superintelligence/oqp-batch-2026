# The power of CGLMP inequalities (Open Quantum Problem 27) in Lean

A Lean 4 formalization of statements for
[Open Quantum Problem 27](docs/OQP_STATEMENT.md), “The power of CGLMP inequalities.”
For two parties with two measurement settings and `d ≥ 2` outcomes, the
projective-measurement theorem bounds the CGLMP value on `Φ_n` by the Fourier-phase
value and classifies equality by a common unitary and a multiplicity `n = d k`.
The [manuscript map](paper/README.md) connects this statement to Theorems 1 and 3
of *The optimal CGLMP measurements on maximally entangled states*.

The formalization also gives tensor-CHSH comparisons with Fourier-phase
measurements at `d = 2^m`: a smaller critical visibility under uniform behaviour
noise for `m ≥ 955`, and greater uniform-input statistical strength than the
Fourier-phase behaviour optimized over input laws for `m ≥ 41`. Further
statements give the fixed CGLMP-witness threshold and properties of a
four-outcome facet for Problem 27.A. The source labels for these statements
come from *CGLMP optimality and the strength of Bell tests*.

## The theorems

[`Challenge.lean`](Challenge.lean) is the statement of record: it imports only Mathlib, copies the
definitions it needs verbatim from the library (namespace `OQP27`), and states each theorem with
`sorry`. [`Solution.lean`](Solution.lean) supplies the proofs. The comparison
configuration is [comparator.json](comparator.json). Three statements for Problem 27.B:

```lean
theorem OQP27.partB_maximizers_are_fourier_phase {d n : ℕ} [NeZero d] [NeZero n] (hd : 2 ≤ d)
    (P : Fin 4 → ZMod d → Matrix (Fin n) (Fin n) ℂ) (hP : ∀ t, OQP27.IsPVM (P t)) :
    OQP27.cglmp d (OQP27.tracialTable ![P 0, P 2] ![P 1, P 3])
        ≤ OQP27.cglmpFourierValue d ∧
      (OQP27.cglmp d (OQP27.tracialTable ![P 0, P 2] ![P 1, P 3])
          = OQP27.cglmpFourierValue d ↔
        ∃ (k : ℕ) (U : Matrix (Fin n) (Fin d × Fin k) ℂ),
          n = d * k ∧ U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
          ∀ (t : Fin 4) (a : ZMod d), P t a =
            U * (OQP27.fourierProjector d t.val a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) * Uᴴ)

theorem OQP27.partB_noise_resistance_not_optimal (m : ℕ) (hm : 955 ≤ m) :
    OQP27.critVisibility (OQP27.TensorCHSH.tensorCHSHTable m)
      < OQP27.critVisibility (OQP27.fourierTable (2 ^ m))

theorem OQP27.partB_kl_discrimination_not_optimal (m : ℕ) (hm : 41 ≤ m) :
    (⨆ μ ∈ {μ : Fin 2 → Fin 2 → ℝ | (∀ x y, 0 ≤ μ x y) ∧ ∑ x, ∑ y, μ x y = 1},
        OQP27.statStrength μ (OQP27.fourierTable (2 ^ m)))
      < OQP27.statStrength (fun _ _ => 1 / 4) (OQP27.TensorCHSH.tensorCHSHTable m)
```

The sixteen declarations in [comparator.json](comparator.json) have the permitted
axiom list `propext`, `Classical.choice` and `Quot.sound`.

In the first theorem `P 0, P 2` are Alice's two measurements, written transposed (the tracial form of
a strategy on the maximally entangled state `Φ_n`), and `P 1, P 3` are Bob's; `IsPVM` means Hermitian
idempotents summing to the identity, and `tracialTable A B` is the behaviour
`q(a,b|x,y) = Re Tr(A x a B y b)/n`, which `OQP27.tracial_table_physical` identifies with the
behaviour of `|Φ_n⟩⟨Φ_n|` with Alice's elements `(A x a)ᵀ` and Bob's `B y b` in the
state-and-tensor-product model. `cglmp d q` is the CGLMP value in
the residual form used in the formalization, with local bound `2` (`OQP27.cglmp_local_bound`).
`fourierProjector d t a` projects onto `ψ_{t,a}(j) = d^{-1/2} exp(-2πi j (a - t/4)/d)`;
`fourierTable d` (`Q_d`) uses `t = 0, 2` for Alice and `t = 1, 3` for Bob and has CGLMP value
`cglmpFourierValue d = I_d^F > 2`. `critVisibility q` is the supremum of the visibilities
`v ∈ [0, 1]` at which the mixture of `q` with uniform noise is local; `statStrength μ q` is the
infimum over local behaviours of the
`μ`-weighted Kullback–Leibler divergence in bits. `TensorCHSH.tensorCHSHTable m` (`T_m`) uses `m`
copies of the CHSH measurements on `Φ_{2^m}`, with the same input on every copy and all outcome bits
kept. The other thirteen theorems are listed with the earlier manuscript labels in the proof outline
below; [docs/FIDELITY.md](docs/FIDELITY.md) maps each phrase of the problem to the Lean.

## How to check

Run the commands below from this directory. A copied-out `lean/` directory is a
complete project with its own license, metadata, dependencies and comparison
configuration.

Requirements: Git, [elan](https://github.com/leanprover/elan), Python 3, and Linux
with `bwrap` (bubblewrap) for the comparison script. The environment is pinned in
[lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json): Lean `v4.35.0-rc4` and Mathlib
`1b3c41969602424bd2f04b3d4f731734e5b00cde`.

```sh
python3 scripts/check-lean-sources.py
lake exe cache get
lake build
./scripts/verify-comparator.sh
```

The source check inspects module headers and file lengths. The build targets the
library, `Challenge`, `Solution`, and the axiom assertions in
[CGLMPBounds/Audit/FinalCheck.lean](CGLMPBounds/Audit/FinalCheck.lean).
`Challenge.lean` uses sixteen deliberate statement holes. The comparison script
compares the declarations in `Solution.lean` with those in `Challenge.lean` using
the configured axioms and the toolchain's bundled kernels.

[Historical verification receipts](verification/RECEIPTS.md) identify checked
commit `d45a91a3cd8e8488b023433dd7feca95fca272a7` and record the source hashes,
commands and logs for those runs.

## Proof outline

Statements are in `Challenge.lean` (namespace `OQP27`); proofs are in the library `CGLMPBounds`
(namespace `CGLMPBounds`, modules under `CGLMPBounds/`).

Source labels below refer to *CGLMP optimality and the strength of Bell tests*;
[paper/README.md](paper/README.md) also maps the current manuscript.

| Source label | Statement | Proof in the library |
|---|---|---|
| Theorem A.1: projective bound and equality case | `partB_maximizers_are_fourier_phase` | `cglmp_projective_bound`, `cglmp_eq_fourier_iff_standard` (`CGLMP/ProjectiveOptimality`), through the companion construction, circulation and partition analysis (`CGLMP/ConditionalMatrixHardyBell`, `Companion/`, `Circulation/`, `Partition/`) and the matrix Hardy bound C.6, `Hardy.fourth_root_matrix_Hardy_bound` (`Hardy/MatrixHardy` and 160 further modules in `Hardy/`) |
| Theorem A.1, attainment: `I_d(Q_d) = I_d^F > 2`, noise threshold `2/I_d^F` | `fourier_attains_cglmp_value` | `fourier_attains_cglmp_value_spec` (`CGLMP/FourierAttain`) |
| (B.1): local bound `2`, attained | `cglmp_local_bound` | `cglmp_le_two`, `exists_mem_localSet_cglmp_eq_two` (`CGLMP/LocalBound`) |
| (B.2): the Fourier-phase projectors form projective measurements | `fourier_projectors_pvm` | `fourierProjector_isPVM` (`Fourier/Basis`) |
| Appendix B: the tracial form on `Φ_n` | `tracial_table_physical` | `tracial_table_physical_spec` (`Quantum/Bridge`) |
| (A.5): the CGLMP-witness threshold, minimized exactly by the Fourier-phase family | `cglmp_witness_tolerance` | `cglmp_witness_tolerance` (`CGLMP/WitnessTolerance`) |
| (A.6): `v_crit(T_m) < 3049/5000 < v_crit(Q_{2^m})` for `m ≥ 955` | `noise_separation_955`, `partB_noise_resistance_not_optimal` | `noise_separation_955` (`Noise/Separation`, with Lemma F.1 in `Fourier/LemmaF1`, `TensorCHSH/Truncation` and the certificates in `Certificates/`) |
| Appendix F.2: the settings of `T_m` are complete rank-one projective measurements on `ℂ^(2^m)` | `tensor_chsh_rank_one_pvm` | `TensorCHSH.tensorProjectorFin_rankOnePVM_spec` (`TensorCHSH/PhysicalRealization`) |
| (F.16): `S_unif(T_m) > (9/14) log₂(4/3) > (16/25) log₂(4/3) > sup_μ S_μ(Q_{2^m})` for `m ≥ 41` | `statistical_separation`, `partB_kl_discrimination_not_optimal` | `statistical_separation_spec` (`Statistics/Separation16`) |
| Proposition G.1: the Bancal–Gisin–Pironio inequality `F ≤ 0` is a facet of the local polytope `C₄` (dimensions 48 and 47); the facet contains a point of the relative interior of the no-signalling polytope; a rational no-signalling behaviour has `F = 1/144`; no bijection of deterministic strategies takes the facet to the CGLMP₄ facet; `F` does not factor through any fusion of outcomes | `bgp_facet`, `bgp_relative_interior_point`, `bgp_no_signalling_violation`, `bgp_not_cglmp_four`, `bgp_no_fusion` | `bgp_facet_spec`, `bgp_relative_interior_point_spec`, `bgp_no_signalling_violation_spec`, `bgp_not_cglmp_four_spec`, `bgp_no_fusion_spec` (`BGP/Facet`, `BGP/FacetRank`, `BGP/Inequivalence`) |

The library `CGLMPBounds` is the import cone of these theorems (467 modules and a root file, about
50,000 lines), plus the axiom pin `CGLMPBounds/Audit/FinalCheck.lean`. The finite certificates (for
example the rank and saturation counts of Proposition G.1 and the rational certificates of
Appendix J) are checked by the kernel (`decide +kernel`), without `native_decide`.

## Citation

See [CITATION.cff](CITATION.cff).

## Licence

Apache License 2.0 ([LICENSE](LICENSE)); see also [NOTICE](NOTICE). Cited papers and dependencies keep
their own licences.
