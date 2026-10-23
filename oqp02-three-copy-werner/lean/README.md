# Three-copy nondistillability of the qutrit Werner state

This directory contains a Lean 4 proof of the qutrit
(`d = 3`), three-copy part of Theorem 2.1 and Corollary 2.2 of the manuscript *Three-copy
nondistillability of qutrit and ququart Werner states*; the manuscript proves them for `d = 3` and
`d = 4`. The central statement is the endpoint
inequality: for every complex `27 × 27` matrix `C` of rank at most two, the three-copy form
`q(C) = q_{1/2}(C)` is nonnegative. From it the proof derives that three copies of the qutrit Werner
state `ρ_{3,α} = (I − α F)/(3(3 − α))` (`F` the flip of the two qutrits) are distillable by local filters
exactly when `α > 1/2` (for `α ≤ 1`), so that for `1/3 < α ≤ 1/2` the state has a negative partial
transpose and three copies of it are not distillable. The question behind these results is Problem 2 of the IQOQI Vienna
Open Quantum Problems, "Undistillability implies PPT?"
(<https://oqp.iqoqi.oeaw.ac.at/undistillability-implies-ppt>).

## Contents

- [Theorem statements](Challenge.lean), [proofs](Solution.lean) and [comparison configuration](comparator.json).
- [Proof library](ThreeCopyQutritWerner/) and [certificate data and receipts](verification/).
- [Paper record](paper/README.md), [paper-to-Lean map](docs/PAPER_TO_LEAN.md) and [statement guide](docs/FIDELITY.md).
- [Citation](CITATION.cff), [formalization metadata](formalization.yaml), [license](LICENSE) and [notice](NOTICE).

## The theorems

[`Challenge.lean`](Challenge.lean) is the statement of record: it imports only Mathlib, repeats verbatim
the definitions of [`ThreeCopyQutritWerner/Basic.lean`](ThreeCopyQutritWerner/Basic.lean), and states 48
theorems with `sorry`. [`Solution.lean`](Solution.lean) proves the same statements from the library
`ThreeCopyQutritWerner/`; [`comparator.json`](comparator.json) lists the 48 theorems in the format of
Lean's Comparator. The headline theorems, in the namespace
`ThreeCopyQutritWerner.Endpoints`:

```lean
def QutritEndpointInequality : Prop :=
  ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
    C.rank ≤ 2 → 0 ≤ endpointEnergy C

theorem qutritEndpointInequality : QutritEndpointInequality

theorem werner_three_three_copy_iff {α : ℝ} (h1 : α ≤ 1) :
    IsThreeCopyFilterDistillable (werner 3 α) ↔ 1 / 2 < α

theorem werner_three_npt_not_three_copy {α : ℝ} (h0 : 1 / 3 < α) (h1 : α ≤ 1 / 2) :
    IsNPT (werner 3 α) ∧ ¬ IsThreeCopyFilterDistillable (werner 3 α)
```

The build requires each of the 48 theorems to depend on exactly the axioms `propext`,
`Classical.choice` and `Quot.sound` (see [How to check](#how-to-check)).

| Theorem | Statement |
|---|---|
| `qutritEndpointInequality` | Theorem 2.1 at `α = 1/2` (claim T2.1a): `q(C) ≥ 0` for every complex `27 × 27` matrix of rank at most two |
| `sharp_minimum` | Theorem 2.1, eq. (4) (T2.1b): for `0 ≤ α ≤ 1/2`, `q_α(C) ≥ (1 − 2α)(1 − α)² ‖C‖_F²` on rank at most two, with equality for some normalized `C` |
| `interior_minimizers` | Theorem 2.1, eq. (5) (T2.1c): for `0 < α < 1/2` every normalized minimizer has the shape of eq. (5) up to a permutation of the sites |
| `minimum_formula_unequal_dims` | Theorem 2.1, unequal local dimensions (T2.1d), the case `2 ≤ dᵢ ≤ 3`: for `0 ≤ α ≤ 1/2`, `q_α(C) ≥ (1 − 2α)(1 − α)² ‖C‖_F²` on rank at most two, with equality for some normalized `C` |
| `werner_three_three_copy_iff` | Corollary 2.2 (C2.2a): three copies of `ρ_{3,α}` are distillable exactly when `α > 1/2` (for `α ≤ 1`) |
| `werner_three_npt_not_three_copy` | Corollary 2.2 (C2.2b): for `1/3 < α ≤ 1/2`, `ρ_{3,α}` is NPT and three copies are not distillable |
| `overlap_le_half` | Corollary 2.2, overlap claim (C2.2c): for `0 ≤ α ≤ 1/2`, every trace-preserving separable operation from three copies to two qubits has overlap at most `1/2` with the maximally entangled state |

The other 41 theorems are the further results of the manuscript that the formalization proves: the
identities of Sections 2 and 3 (Proposition 3.1, eqs. (6)–(11)), the Werner-state facts of Section 1, the
PPT region `α ≤ 1/3`, distillability for `α > 1/2`, the attainment of the sharp curve, the zero families
of Theorem 5.1 (inclusion "⊇") and the analytic inputs of Appendix C, Section 6.2 (the full-rank family),
the implications from T2.1a, and the soundness of an exact certificate (Section 4.1). All are listed with
their manuscript locations in [docs/FIDELITY.md](docs/FIDELITY.md), and
[docs/PAPER_TO_LEAN.md](docs/PAPER_TO_LEAN.md) records the correspondence between numbered statements and equations of the
manuscript and the Lean development.

Reading the statements:

- `endpointEnergy C = q_{1/2}(C)`, where `q_α(C) = N − α A + α² B − α³ T₀` (eq. (3)) with `N = ‖C‖_F²`,
  `A = Σᵢ ‖Trᵢ C‖_F²`, `B = Σ_{i<j} ‖Tr_{ij} C‖_F²`, `T₀ = |Tr C|²` and unnormalized partial traces over
  the three sites of `C`.
- `werner d α = (I − α F)/(d (d − α))` on `ℂ^d ⊗ ℂ^d` (eq. (1)); `IsNPT ρ` says that the partial transpose
  of `ρ` (on the second factor) is not positive semidefinite.
- `IsThreeCopyFilterDistillable ρ`: for some local filters `A`, `B` from `(ℂ^d)^{⊗3}` to `ℂ²`, the operator
  `(A ⊗ B) ρ^{⊗3} (A ⊗ B)†` on two qubits is NPT. The link with `q_α` is eq. (6): for a coefficient matrix
  `C`, `⟨vec C, (ρ_{3,α}^{⊗3})^Γ vec C⟩ = (3(3 − α))^{-3} q_α(C)` (`three_copy_expectation`), the Schmidt
  rank of `vec C` is the rank of `C` (`schmidtRank_vec`), and filter distillability is detection by a
  vector of Schmidt rank at most two (`filter_iff_rank_two_detectable`).

## How to check

Run these commands from this directory, containing `lean-toolchain` and `lakefile.toml`. The complete `lean/` directory can also be copied out and used as a standalone project; keep its source, scripts, certificate data, configuration and license together.

Requirements: Linux, Git, Python 3 (the data-transport elaborators decode the compressed data files with it during the build) and [elan](https://github.com/leanprover/elan). [lean-toolchain](lean-toolchain) pins Lean `v4.35.0-rc4`; [lake-manifest.json](lake-manifest.json) pins Mathlib at commit `1b3c4196`.

```text
python3 scripts/check-lean-sources.py
python3 scripts/check-challenge-definitions.py
lake exe cache get
lake build
```

The build targets include the library, `Challenge`, `Solution` and [FinalCheck.lean](ThreeCopyQutritWerner/Audit/FinalCheck.lean). `Challenge.lean` uses 48 statement placeholders; `Solution.lean` supplies their proofs. `FinalCheck.lean` requires each listed theorem to depend on exactly `propext`, `Classical.choice` and `Quot.sound`.

[Historical verification receipts](verification/RECEIPTS.md) record commands, outputs and resource use for checked formalization commit `787448536a506e69c3f15d953257f224f095c5eb`. The recorded full build used 8 CPUs and 336 GiB of memory and took 7.3 hours. The comparison configuration is [comparator.json](comparator.json); the existing [comparison script](scripts/verify-comparator.sh) documents its invocation and Linux sandbox requirements.

The comparison script also requires bubblewrap (`bwrap`). Run it from this directory:

```bash
./scripts/verify-comparator.sh
```

## Proof outline

Theorem 2.1 reduces to its endpoint `α = 1/2` through the continuation identity of Proposition 3.1. The
endpoint inequality is proved from an exact certificate of the form of Section 4.1 of the manuscript.
Write a rank-two `C = X Y†` with `X` a `27 × 2` matrix and let `p` be the bivector of the two columns of `X`. For the
features `z_h = vec C ⊗ p ⊗ p`, `z_m = vec C ⊗ p ⊗ p̄` and `z_a = vec C ⊗ p̄ ⊗ p̄`, and with `Θ` the operator of
Section 4.1 (the identity on the four registers of `p ⊗ p`), the identity

`Π_h Θ Π_h = G_h + Π_h Γ₃₄(G_m) Π_h + Π_h Γ₁₂₃₄(G_a) Π_h`   (eq. (14))

with positive semidefinite `G_h`, `G_m`, `G_a` gives
`‖p‖⁴ q(C) = ⟨z_h, G_h z_h⟩ + ⟨z_m, G_m z_m⟩ + ⟨z_a, G_a z_a⟩ ≥ 0` (eq. (15)), and rank one is handled
separately. The certificate is stated in symmetry-reduced coordinates: the symmetries of the problem split
the six-register space into a holomorphic, a mixed and an antiholomorphic sector and these into 414 blocks
indexed by local types (122, 169 and 123 blocks). The certificate data are the manuscript's rational trial
tuple together with an exact rational correction on eight blocks that solves the coefficient equations
exactly. This correction differs from the one defined by eq. (20) of the manuscript; both solve the same
linear equations. The source blocks are an exact Gram factor with this correction, and the transfer of the
sources to the holomorphic sector, the outputs and the 122 residual blocks are exact rational matrices. The
Lean kernel checks every number: positivity of each block (Gram forms, and face-supported blocks with an exact
diagonally dominant residual), the transfer through the three tensor axes (packed natural-number
arithmetic evaluated by the kernel), the output and residual identities, and the reconstruction of the
operator identity on the six registers from the reduced blocks. The data enter as literal files under
`verification/matrix-literals/` and `verification/finite-integer-literals/` (1,675 files: 802 compressed
integer arrays, each pinned by its SHA-256 in the Lean source, and 873 hexadecimal tables); every
statement about them is checked by the kernel. No floating-point or interval bound enters the proof.

| Manuscript | Lean | Module |
|---|---|---|
| Theorem 2.1 at `α = 1/2` (T2.1a) | `x2_qutritEndpointInequality` | `CertificateX2FinalProof` |
| Section 4.1, eqs. (12)–(15): an exact certificate implies T2.1a | `qutritEndpointInequality_of_certificate` | `CertificateReduction` |
| Section 4: the symmetry-reduced certificate and its reconstruction on the six registers | `X2ReducedBridge`, `x2_qutritEndpointInequality_of_facts'` | `CertificateX2Reduced`, `CertificateX2BridgeTriple` |
| Exact source blocks and their positivity | `x2SourceM_posSemidef`, `x2SourceA_posSemidef` | `CertificateX2IntegrationSources` |
| Transfer of the sources (input stage and contraction core) | `X2.InGS1.hT0`, `X2.InGA1.hT0`, `X2.InGA2.hT0` | `CertificateX2InputGlueS1`, `…A1`, `…A2` |
| Outputs, residual identities and residual positivity | `x2_qutritEndpointInequality_of_outputs`, `x2HNum_psd` | `CertificateX2FinalCarrier`, `CertificateX2HBlockPsdHFamily` |
| Proposition 3.1, eq. (9) | `energy_sub_sharpCurve_mul_invN` | `Continuation` |
| Theorem 2.1, eqs. (4), (5), and Corollary 2.2 from T2.1a | `sharpCurve_mul_invN_le_energy_of_endpointEnergy_nonneg`, `isInteriorMinimizerShape_of_isMin`, `isThreeCopyFilterDistillable_werner_three_iff_of_endpoint`, `werner_three_maxEntOverlap_le_of_endpoint` | `TwoCutMain`, `Interior`, `WernerState`, `Overlap` |
| Theorem 5.1, inclusion "⊇" | `isNormalizedHalfSingularZero_of_isQutritZeroFamilyMember` | `ZeroFamilies` |
| Appendix C, analytic inputs | `appCInput1_proved`, `appCInput2_product_ray`, `appCInput3_proved` | `ZeroReserveRigidity`, `AppendixCProductRay`, `ThinOriginalClassification` |

Module names are relative to `ThreeCopyQutritWerner/`. The library consists of the 3,616 modules that
`Solution.lean` imports, directly or indirectly, and the axiom check; it contains no `sorry` and no
`axiom`.

## Paper

*Three-copy nondistillability of qutrit and ququart Werner states*, Physical Superintelligence (PSI),
manuscript of 21 October 2026. Paper in preparation; see [paper/README.md](paper/README.md).

## Citation

See [CITATION.cff](CITATION.cff). Please cite the paper of record ([paper/README.md](paper/README.md))
for the mathematics.

## License

Apache License 2.0 ([LICENSE](LICENSE)); see also [NOTICE](NOTICE). Mathlib and the Lean toolchain keep
their own licences.
