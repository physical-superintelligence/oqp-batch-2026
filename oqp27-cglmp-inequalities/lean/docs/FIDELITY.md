# Fidelity: Open Quantum Problem 27 and the Lean statements

This file maps each phrase of Problem 27 ([OQP_STATEMENT.md](OQP_STATEMENT.md)) and the results of
the formalization source to the definitions and theorems of
[`Challenge.lean`](../Challenge.lean). Labels such as Theorem A.1 or (F.16) refer
to *CGLMP optimality and the strength of Bell tests*. The
[manuscript map](../paper/README.md) gives the correspondence with Theorems 1 and 3
of *The optimal CGLMP measurements on maximally entangled states*.

All definitions used by the statements are copied into `Challenge.lean` from `CGLMPBounds/Defs/`
(Scenario, CGLMP, CGLMPValue, Quantum, Fourier, Visibility, Statistics, TensorMeasurement,
QuantumGeneral, BGP) with the same statements and bodies, under the namespace `OQP27` instead of
`CGLMPBounds` (Lean shares within one file the auxiliary proofs that numerals carry, so one-file
copies are new constants with the library's bodies). The bound `3 x + a < 6` inside `bgpIndex` is
proved by a term instead of `omega`, because the proof `omega` builds contains a constant named after
the file; the function is the same. The tables below write names without the namespace.
`Solution.lean` repeats the same block and proves that each copy agrees with the library definition
(`OQP27.Bridge`: `rfl` for the definitions, `Iff` for the five structures). [comparator.json](../comparator.json) selects the declarations and permits
`propext`, `Quot.sound` and `Classical.choice`.

## 1. The setting

| Problem 27 | Lean | Notes |
|---|---|---|
| "the case (N,M,K)=(2,2,d)" | `Table α β := Fin 2 → Fin 2 → α → β → ℝ`, read as `q(a,b\|x,y)`; `d` outcomes are `ZMod d` | two parties, two settings per party (`Fin 2`), `d` outcomes |
| "local polytope C" | `localSet α β := convexHull ℝ (Set.range detTable)` | deterministic tables `detTable s`, `s = (a₀, a₁, b₀, b₁)` |
| "no-signalling polytope P" | `{q \| IsNoSignalling q}` | nonnegative, normalized in every context, marginals independent of the other party's input |
| "the CGLMP inequality" | `cglmp d q ≤ 2`, with `cglmp d q = 4 - 2 S_d(q)/(d - 1)` and `S_d(q) = Σ_{x,y} E_q r_{xy}` | residual form (B.1): `r₀₀ = r₁₁ = [a - b]_d`, `r₁₀ = [b - a]_d`, `r₀₁ = [b - a - 1]_d` with `[·]_d = ZMod.val`; local bound `2`, attained: `OQP27.cglmp_local_bound` |

**The CGLMP functional.** `cglmp` is the residual form of the formalization source. Its local bound is 2
and is attained (`OQP27.cglmp_local_bound`), and the Fourier-phase value `I_d^F` exceeds 2
(`OQP27.fourier_attains_cglmp_value`). Dictionary to the probability expression in [CGLMP]: write
CGLMP's inputs as `A₁ =` Alice's input 1, `A₂ =` Alice's input 0, `B₁ =` Bob's input 1, `B₂ =` Bob's
input 0, with outcomes unchanged. CGLMP's four residuals `[A₁ - B₁]`, `[B₁ - A₂ - 1]`, `[A₂ - B₂]`,
`[B₂ - A₁]` are then `r₁₁`, `r₀₁`, `r₀₀`, `r₁₀`, and for each of them
`Σ_k (1 - 2k/(d-1)) (P(r = k) - P(r = d-1-k)) = 1 - 2 E[r]/(d-1)` (for odd `d` the middle value has
weight 0), so `cglmp d q` equals the CGLMP value on every normalized behaviour, with no change of
normalization.

## 2. Problem 27.B

### "the observables maximally violating the CGLMP inequality on a maximally entangled state"

| Phrase | Lean |
|---|---|
| "observables" | projective measurements: `IsPVM P` (Hermitian, idempotent, summing to 1; zero projectors and unequal ranks allowed) |
| "a maximally entangled state" | `Φ_n` in any dimension `n ≥ 1`, through the tracial form `tracialTable A B x y a b = Re Tr(A x a * B y b) / n` |
| "maximally violating" | the CGLMP value of a strategy equals the maximum over all projective strategies on all `Φ_n`, which is `cglmpFourierValue d`: `OQP27.partB_maximizers_are_fourier_phase` (upper bound) and `OQP27.fourier_attains_cglmp_value` (attained) |

**The tracial form.** Four projective measurements are written in the tracial form
`(P 0, P 1, P 2, P 3) = (A₀ᵀ, B₀, A₁ᵀ, B₁)`: Alice's physical measurements are the transposes of
`P 0` and `P 2`. `OQP27.tracial_table_physical` proves that the behaviour of `|Φ_n⟩⟨Φ_n|` with
Alice's elements `(A x a)ᵀ` and Bob's `B y b`, computed as `Re Tr(ρ (E ⊗ F))` in the
state-and-tensor-product model `quantumTable`, equals `tracialTable A B`, and that the transposes of
a PVM form a PVM. Physically, Alice's Fourier bases in the equality case are complex conjugated. The
common unitary `U` of the equality case identifies `ℂⁿ` with `ℂ^d ⊗ ℂ^k`, and `Ū ⊗ U` maps
`Φ_d ⊗ Φ_k` to `Φ_n`: up to local unitaries that preserve the state, the maximal violators are the
Fourier-phase measurements on a `Φ_d` factor, with an idle `Φ_k` factor.

### "of a very specific form, involving measurements in computational basis, transformed by only discrete Fourier transformation and diagonal unitaries"

`fourierProjector d t a` is the projector onto
`fourierVector d t a j = d^{-1/2} exp(-2πi j (a - t/4)/d)`, `j = 0, …, d - 1`: the `a`-th
discrete-Fourier-transform vector after the diagonal phase `j ↦ exp(2πi j t/(4d))`. Alice uses
`t = 0, 2` and Bob `t = 1, 3` (`fourierTable d`, the behaviour `Q_d`). In the Lean statements the
Fourier-phase elements are rank one by definition (`fourierProjector` projects onto one vector).

**The measurement settings of [CGLMP].** With the input dictionary of section 1, `fourierTable d`
equals, entry by entry and with the same outcome labels, the behaviour on `Φ_d` of the measurements of
[CGLMP] (phases 0 and 1/2 for Alice, 1/4 and -1/4 for Bob). The tracial projectors are CGLMP's
(Alice's transposed) conjugated by the common diagonal unitary `D = diag(e^{iπj/d})`, and `D̄ ⊗ D`
leaves `Φ_d` unchanged.

### "Show that this is necessarily the case." (true for projective measurements)

`OQP27.partB_maximizers_are_fourier_phase`: for `d ≥ 2`, `n ≥ 1` and projective `P`,
`cglmp d (tracialTable ![P 0, P 2] ![P 1, P 3]) ≤ cglmpFourierValue d`, with equality if and only if
`n = d k` and there is a unitary `U : ℂⁿ → ℂ^d ⊗ ℂ^k` (written as a matrix indexed by
`Fin n × (Fin d × Fin k)` with `U Uᴴ = 1` and `Uᴴ U = 1`) such that
`P t a = U (fourierProjector d t a ⊗ 1_k) Uᴴ` for all `t`, `a` (Theorem A.1).

- Every dimension `n` is covered, with an explicit multiplicity `k`. For `n = d` the maximal violators
  are exactly the rank-one Fourier-phase measurements up to a common unitary (`k = 1`); when `d` does
  not divide `n`, the value on `Φ_n` stays strictly below `I_d^F`.
- Non-vacuity: `OQP27.fourier_attains_cglmp_value` (`Q_d` attains `I_d^F > 2`) and
  `OQP27.fourier_projectors_pvm` (the Fourier-phase projectors form PVMs).

### "Show also that these measurements realize the highest resistance of violation to noise" (false in the global sense; true for the CGLMP witness)

1. **Global white-noise resistance (false at `d = 2^m`, `m ≥ 955`).** `critVisibility q` is the
   supremum of `v ∈ [0, 1]` such that `v q + (1 - v) u` is local, `u` the uniform table (`noisy`,
   `uniformTable`); a smaller value means more noise is needed to make the behaviour local.
   `OQP27.partB_noise_resistance_not_optimal`: for every `m ≥ 955`,
   `critVisibility (T_m) < critVisibility (Q_{2^m})`; the explicit constant `3049/5000` is in
   `OQP27.noise_separation_955` (equation (A.6)).
2. **Threshold of the CGLMP witness (true).** `OQP27.cglmp_witness_tolerance` (equation (A.5)): for a
   projective strategy with `I_d(q) > 2`, the noisy behaviour violates the CGLMP inequality exactly
   when `v > 2/I_d(q)`; this threshold is at least `2/I_d^F`, with equality exactly in the
   Fourier-phase case of Theorem A.1.

The comparison strategy `T_m` (`TensorCHSH.tensorCHSHTable m`) uses `m` copies of the CHSH
measurements (`Z`, `X` for Alice; `(Z ± X)/√2` for Bob) on `Φ_2^{⊗m} = Φ_{2^m}`, with the same input
on every copy and all `m` outcome bits kept. `OQP27.tensor_chsh_rank_one_pvm` proves that its four
settings are complete rank-one projective measurements on `ℂ^(2^m)`; `T_m` is by definition the
tracial table of these measurements, so `OQP27.tracial_table_physical` applies to it as to `Q_{2^m}`.
`T_m` has outcomes `Fin m → Bool` (bit strings) and `Q_{2^m}` has outcomes `ZMod (2^m)`; both sets
have `2^m` elements, so both strategies belong to the scenario `(2, 2, 2^m)`.

The noise is uniform noise on the behaviour. For rank-one projective measurements on `Φ_d` this is the
behaviour of the isotropic state `v |Φ_d⟩⟨Φ_d| + (1 - v) I/d²`; the library proves this identity for
outcomes `Fin d` (`CGLMPBounds.isotropic_noise_spec` in `CGLMPBounds/Quantum/General.lean`).

### "and the best discrimination against classical realism in the sense of Kullback–Leibler divergence" (false at `d = 2^m`, `m ≥ 41`)

`statStrength μ q` is the statistical strength of [VDGG]: the infimum over local behaviours `ℓ` of
`Σ_{x,y} μ(x,y) D(q(·|x,y) ‖ ℓ(·|x,y))`, where `D` is the Kullback–Leibler divergence in bits
(`relEntropy`, with value `∞` when the support condition fails), and `μ` is the law of the inputs.
`OQP27.partB_kl_discrimination_not_optimal`: for every `m ≥ 41`,
`⨆_μ statStrength μ (Q_{2^m}) < statStrength unif (T_m)`, the supremum taken over all input laws
(equation (F.16); explicit constants in `OQP27.statistical_separation`).

- The comparison gives `Q_{2^m}` its best input law and `T_m` the uniform one, so it holds both when
  the input law is fixed to uniform and when each strategy may choose its input law.

## 3. Problem 27.A: four-outcome facet

The theorems below describe the four-outcome facet defined by `bgpFunctional`,
inequality (G.1) of the formalization source. The bibliography is in
[CITATION.cff](../CITATION.cff) and [formalization.yaml](../formalization.yaml).
The counterexample is a facet, so in particular a face; it addresses the
problem's formulations in terms of faces and facets.

| Phrase | Lean |
|---|---|
| "every face of the local polytope C" | `OQP27.bgp_facet`: for `d = 4`, `F ≤ 0` holds on `C₄` (`F = bgpFunctional`, (G.1)), `C₄` has affine dimension 48 and the face `C₄ ∩ {F = 0}` has affine dimension 47, so `F ≤ 0` defines a facet (dimensions as `Module.finrank ℝ (vectorSpan ℝ ·)`) |
| "which is not already contained in a face of the no-signalling polytope P" | `OQP27.bgp_relative_interior_point`: the facet contains a point `p̄` of the relative interior (`intrinsicInterior ℝ`) of `P₄`, so the only face of `P₄` containing the facet is `P₄` itself; `OQP27.bgp_no_signalling_violation`: a rational no-signalling behaviour has `F = 1/144 > 0` |
| "is of CGLMP type, i.e., an inequality of the form first written out in [CGLMP]" | `OQP27.bgp_not_cglmp_four`: no bijection of deterministic strategies maps the saturating strategies of `F` onto those of the CGLMP₄ functional (the library counts 72 against 80); relabellings of parties, settings and outcomes induce such bijections, and a facet is determined by its saturating vertices |
| "but possibly lifted from lower dimensions by fusing together some outcomes" | `OQP27.bgp_no_fusion`: for outcome maps that identify two outcomes in some setting, `F` restricted to deterministic strategies does not factor through the fused strategies, for any target outcome sets and any target function |

**The two readings of "of CGLMP type".** The CGLMP₄ facet up to relabelling and an outcome-fusion
lifting of an inequality with fewer outcomes are excluded by `OQP27.bgp_not_cglmp_four` and
`OQP27.bgp_no_fusion`. The fusion statement is about the values of `F` on deterministic strategies,
so it also rules out positive rescalings, affine shifts and additions of no-signalling identities.
