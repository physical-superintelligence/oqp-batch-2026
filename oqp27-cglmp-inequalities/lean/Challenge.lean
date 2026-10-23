module

public import Mathlib

@[expose] public section

/-!
# The power of CGLMP inequalities (Open Quantum Problems, Problem 27): statement of record

Problem 27 of the IQOQI Vienna list of Open Quantum Problems, "The power of CGLMP inequalities"
(codified by R. Gill), reads (citation markers as in `docs/OQP_STATEMENT.md`):

> In the setting of Problem 26, consider especially the case (N,M,K)=(2,2,d).
>
> **Problem 27.A.** Show that every face of the local polytope C, which is not already contained
> in a face of the no-signalling polytope P is of CGLMP type, i.e., an inequality of the form first
> written out in [CGLMP], but possibly lifted from lower dimensions by fusing together some
> outcomes.
>
> **Problem 27.B.** Numerically, the observables maximally violating the CGLMP inequality on a
> maximally entangled state are of a very specific form [DKZ], involving measurements in
> computational basis, transformed by only discrete Fourier transformation and diagonal unitaries
> [CGLMP]. Show that this is necessarily the case. Show also that these measurements realize the
> highest resistance of violation to noise, and the best discrimination against classical realism
> in the sense of Kullback–Leibler divergence [VDGG].

The theorems below prove the following. `Solution.lean` proves each of them; Comparator checks that
the statements there are exactly these, using only the axioms `propext`, `Quot.sound` and
`Classical.choice`.

* 27.B, "necessarily the case": **true for projective measurements**,
  `OQP27.partB_maximizers_are_fourier_phase` (with `OQP27.fourier_attains_cglmp_value`).
* 27.B, "highest resistance of violation to noise": **false** for global white-noise resistance at
  `d = 2^m`, `m ≥ 955`, `OQP27.partB_noise_resistance_not_optimal`; true for the threshold of the
  CGLMP witness itself, `OQP27.cglmp_witness_tolerance`.
* 27.B, "best discrimination ... in the sense of Kullback–Leibler divergence": **false** at
  `d = 2^m`, `m ≥ 41`, `OQP27.partB_kl_discrimination_not_optimal`.
* 27.A: **false**. This was shown by Bancal, Gisin and Pironio (J. Phys. A 43, 385303 (2010)) with a
  four-outcome facet; `OQP27.bgp_facet`, `OQP27.bgp_relative_interior_point`,
  `OQP27.bgp_no_signalling_violation`, `OQP27.bgp_not_cglmp_four` and `OQP27.bgp_no_fusion`
  re-certify their facet. (A facet is in particular a face, so this also answers the literal
  wording.)

## Conventions

* A behaviour is a table `q x y a b = q(a,b|x,y)` with inputs `x y : Fin 2` (`Table`). With `d`
  outcomes per party the outcomes are `ZMod d`. `localSet` is the local polytope `C` (convex hull of
  the deterministic tables) and `IsNoSignalling` the no-signalling polytope `P`.
* `cglmp d q` is the CGLMP value `I_d(q) = 4 - 2 S_d(q)/(d - 1)`, in the residual form (B.1) of the
  paper of record; its local bound is `2` (`OQP27.cglmp_local_bound`). `docs/FIDELITY.md` relates it
  to the probability expression of Collins, Gisin, Linden, Massar and Popescu (with the two inputs of
  each party swapped).
* Measurements are projective (`IsPVM`: Hermitian idempotents summing to the identity; zero
  projections and unequal ranks allowed). On the maximally entangled state `Φ_n` the behaviour of
  Alice's measurements `Aᵀ` and Bob's `B` is `tracialTable A B`, `q(a,b|x,y) = Re Tr(A x a B y b)/n`
  (`OQP27.tracial_table_physical` proves this against the state-and-tensor-product model
  `quantumTable (phiState n)`). Alice's matrices therefore appear transposed: four measurements
  are written `(P 0, P 1, P 2, P 3) = (A₀ᵀ, B₀, A₁ᵀ, B₁)` and the behaviour is
  `tracialTable ![P 0, P 2] ![P 1, P 3]`.
* The Fourier-phase measurements `fourierProjector d t`, `t = 0, 1, 2, 3`, project onto
  `ψ_{t,a}(j) = d^{-1/2} exp(-2πi j (a - t/4)/d)`: discrete-Fourier-transform vectors of the
  computational basis with a diagonal phase. `fourierTable d` (`Q_d`) uses `t = 0, 2` for Alice and
  `t = 1, 3` for Bob, and `cglmpFourierValue d` is its CGLMP value `I_d^F`.
* `critVisibility q` is the largest visibility `v ∈ [0, 1]` at which `v q + (1 - v) u` (uniform
  noise `u`) is local; smaller means more resistant to noise.
* `statStrength μ q` is the statistical strength of van Dam, Gill and Grünwald: the infimum over
  local behaviours `ℓ` of `Σ_{x,y} μ(x,y) D(q(·|x,y) ‖ ℓ(·|x,y))`, a Kullback–Leibler divergence in
  bits per trial under the input law `μ`.
* `TensorCHSH.tensorCHSHTable m` (`T_m`) uses `m` copies of the CHSH measurements on
  `Φ_2^{⊗m} = Φ_{2^m}`, the same input on every copy, keeping all `m` outcome bits: two settings and
  `2^m` outcomes per party, like `Q_{2^m}`, but with outcomes labelled by bit strings.

## Definitions

Every definition below is copied from the library module named in the comment above it, with the
same statement and body; only the namespace `CGLMPBounds` is renamed to `OQP27`, and the bound
`3 x + a < 6` inside `bgpIndex` is proved by a term instead of `omega` (whose proof would contain a
constant named after the file; the function is the same). (The library keeps
these definitions in ten files. Lean shares, within one file, the auxiliary proofs that numerals such
as `2 : ℂ` carry, so copies gathered in one file cannot be the very same constants as the library's;
under their own namespace they are new constants with the same bodies.) Their docstrings are those of
the library and may name library files and lemmas. `Solution.lean` repeats this block and proves that
each definition agrees with its library counterpart, so the library's theorems apply to the statements
below.
-/

-- Copied from `CGLMPBounds/Defs/Scenario.lean`, namespace `CGLMPBounds` renamed to `OQP27`.

namespace OQP27

noncomputable section

/-- A real table `q x y a b`, read as `q(a,b|x,y)`: `x` is Alice's input, `y` is Bob's input and
`a`, `b` are their outcomes. Neither positivity nor normalisation is built in. -/
abbrev Table (α β : Type*) := Fin 2 → Fin 2 → α → β → ℝ

/-- A behaviour: a nonnegative table that is normalised in each context `(x, y)`. -/
structure IsBehaviour {α β : Type*} [Fintype α] [Fintype β] (q : Table α β) : Prop where
  /-- All entries are nonnegative. -/
  nonneg : ∀ x y a b, 0 ≤ q x y a b
  /-- Each context is normalised. -/
  sum_eq_one : ∀ x y, ∑ a, ∑ b, q x y a b = 1

/-- The no-signalling polytope `P_d`: behaviours whose one-party marginals are independent of the
other party's input. -/
structure IsNoSignalling {α β : Type*} [Fintype α] [Fintype β] (q : Table α β) : Prop where
  /-- The table is a behaviour. -/
  isBehaviour : IsBehaviour q
  /-- Alice's marginal does not depend on Bob's input. -/
  margA_indep : ∀ x y y' a, ∑ b, q x y a b = ∑ b, q x y' a b
  /-- Bob's marginal does not depend on Alice's input. -/
  margB_indep : ∀ x x' y b, ∑ a, q x y a b = ∑ a, q x' y a b

/-- A deterministic assignment `(a₀, a₁, b₀, b₁)`: `s.1 x` is Alice's outcome on input `x` and
`s.2 y` is Bob's outcome on input `y`. -/
abbrev Strategy (α β : Type*) := (Fin 2 → α) × (Fin 2 → β)

/-- The deterministic table `q_s(a,b|x,y) = 1{a = a_x, b = b_y}`. -/
def detTable {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Strategy α β) : Table α β :=
  fun x y a b => if a = s.1 x ∧ b = s.2 y then 1 else 0

/-- The Bell-local set (the local polytope `C_d`): the convex hull of the deterministic tables. -/
def localSet (α β : Type*) [DecidableEq α] [DecidableEq β] : Set (Table α β) :=
  convexHull ℝ (Set.range (detTable (α := α) (β := β)))

/-- The uniform table `u(a,b|x,y) = 1 / (|α| |β|)`. For `α = β = ZMod d` this is `u_d = d⁻²`. -/
def uniformTable (α β : Type*) [Fintype α] [Fintype β] : Table α β :=
  fun _ _ _ _ => 1 / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ))

/-- The uniform-noise mixture `v q + (1 - v) u` at visibility `v`. -/
def noisy {α β : Type*} [Fintype α] [Fintype β] (v : ℝ) (q : Table α β) : Table α β :=
  v • q + (1 - v) • uniformTable α β

end

end OQP27

-- Copied from `CGLMPBounds/Defs/CGLMP.lean`, namespace `CGLMPBounds` renamed to `OQP27`.

namespace OQP27

noncomputable section

/-- The oriented residual `r_{xy}(a,b) ∈ {0, …, d-1}` of (B.1):
`r₀₀ = [a-b]_d`, `r₁₁ = [a-b]_d`, `r₁₀ = [b-a]_d`, `r₀₁ = [b-a-1]_d`. -/
def residual (d : ℕ) (x y : Fin 2) (a b : ZMod d) : ℕ :=
  if x = y then (a - b).val else if x = 1 then (b - a).val else (b - a - 1).val

/-- `S_d(q) = ∑_{x,y} E_q r_{xy}`, equation (B.1). -/
def cglmpS (d : ℕ) [NeZero d] (q : Table (ZMod d) (ZMod d)) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, (residual d x y a b : ℝ) * q x y a b

/-- The CGLMP value `I_d(q) = 4 - 2 S_d(q) / (d - 1)`, equation (B.1). -/
def cglmp (d : ℕ) [NeZero d] (q : Table (ZMod d) (ZMod d)) : ℝ :=
  4 - 2 * cglmpS d q / ((d : ℝ) - 1)

end

end OQP27

-- Copied from `CGLMPBounds/Defs/CGLMPValue.lean`, namespace `CGLMPBounds` renamed to `OQP27`.

namespace OQP27

noncomputable section

/-- The Fourier value (A.1), `I_d^F = 4/(d(d-1)) Σ_{h=1}^{d-1} (d - h) sec(π h/(2d))`, with
`sec t = 1 / cos t`; `Finset.Ico 1 d = {1, …, d-1}`. -/
def cglmpFourierValue (d : ℕ) : ℝ :=
  4 / ((d : ℝ) * ((d : ℝ) - 1)) *
    ∑ h ∈ Finset.Ico 1 d, ((d : ℝ) - h) / Real.cos (Real.pi * h / (2 * d))

end

end OQP27

-- Copied from `CGLMPBounds/Defs/Quantum.lean`, namespace `CGLMPBounds` renamed to `OQP27`.

namespace OQP27

/-- A projective measurement on `ℂⁿ` with outcomes in `α`: orthogonal projections (Hermitian
idempotents) summing to the identity. Zero projections and unequal ranks are allowed. -/
structure IsPVM {n : ℕ} {α : Type*} [Fintype α] (P : α → Matrix (Fin n) (Fin n) ℂ) : Prop where
  /-- Each element is Hermitian. -/
  isHermitian : ∀ a, (P a).IsHermitian
  /-- Each element is idempotent. -/
  mul_self : ∀ a, P a * P a = P a
  /-- The elements sum to the identity. -/
  sum_eq_one : ∑ a, P a = 1

noncomputable section

/-- The behaviour of tracial projective measurements on `Φ_n`:
`q(a,b|x,y) = n⁻¹ Re Tr(A x a * B y b)`. Here `A x = P^{2x}` is the tracial (transposed) form `A_xᵀ`
of Alice's measurement for input `x`, and `B y = P^{1+2y}` is Bob's measurement for input `y`.
The trace of a product of two projections is real; `Re` only fixes the type. -/
def tracialTable {n : ℕ} {α β : Type*} (A : Fin 2 → α → Matrix (Fin n) (Fin n) ℂ)
    (B : Fin 2 → β → Matrix (Fin n) (Fin n) ℂ) : Table α β :=
  fun x y a b => (Matrix.trace (A x a * B y b)).re / n

end

end OQP27

-- Copied from `CGLMPBounds/Defs/Fourier.lean`, namespace `CGLMPBounds` renamed to `OQP27`.

namespace OQP27

noncomputable section

/-- The Fourier-phase vector `ψ_{t,a}` of (B.2): `ψ_{t,a}(j) = d^{-1/2} e^{-2πi j (a - t/4)/d}`
for `j ∈ {0, …, d-1}`; the outcome `a ∈ ℤ_d` enters through its representative
`a.val ∈ {0, …, d-1}`. -/
def fourierVector (d t : ℕ) (a : ZMod d) (j : Fin d) : ℂ :=
  (((Real.sqrt d)⁻¹ : ℝ) : ℂ) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) * (((a.val : ℕ) : ℂ) - (t : ℂ) / 4)) / d)

/-- The standard tracial projector `Π^t_a = |ψ_{t,a}⟩⟨ψ_{t,a}|` of (B.2). -/
def fourierProjector (d t : ℕ) (a : ZMod d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec (fourierVector d t a) (star (fourierVector d t a))

/-- The Fourier-phase behaviour `Q_d`: Alice's tracial measurements `P^{2x} = Π^{2x}` and Bob's
measurements `P^{1+2y} = Π^{1+2y}` on `Φ_d`. -/
def fourierTable (d : ℕ) : Table (ZMod d) (ZMod d) :=
  tracialTable (fun x a => fourierProjector d (2 * x.val) a)
    (fun y b => fourierProjector d (1 + 2 * y.val) b)

end

end OQP27

-- Copied from `CGLMPBounds/Defs/Visibility.lean`, namespace `CGLMPBounds` renamed to `OQP27`.

namespace OQP27

noncomputable section

/-- Global critical visibility of a table under uniform noise:
the supremum of the visibilities `v ∈ [0,1]` at which `v q + (1 - v) u` is Bell-local. -/
def critVisibility {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (q : Table α β) : ℝ :=
  sSup {v : ℝ | 0 ≤ v ∧ v ≤ 1 ∧ noisy v q ∈ localSet α β}

end

end OQP27

-- Copied from `CGLMPBounds/Defs/Statistics.lean`, namespace `CGLMPBounds` renamed to `OQP27`; only the definitions used below.

namespace OQP27

noncomputable section

open scoped ENNReal

/-- Relative entropy in bits of two finite real vectors, `D(p‖r) = Σ_z p_z log₂(p_z / r_z)`, with
the usual extended-value conventions: terms with `p_z = 0` contribute `0`, and `D(p‖r) = ∞` as soon
as some `p_z ≠ 0` has `r_z = 0`. For probability vectors the finite sum is nonnegative (Gibbs'
inequality, proved as `relEntropy_sum_nonneg`), so `ENNReal.ofReal` does not truncate it there. -/
def relEntropy {ι : Type*} [Fintype ι] (p r : ι → ℝ) : ℝ≥0∞ :=
  if ∀ z, r z = 0 → p z = 0 then ENNReal.ofReal (∑ z, p z * Real.logb 2 (p z / r z)) else ∞

/-- Statistical strength (B.5) in bits per complete trial,
`S_μ(q) = min_{ℓ ∈ C_d} Σ_{x,y} μ_{xy} D(q_{xy} ‖ ℓ_{xy})`, for a weight `μ x y` on the four input
pairs (an input law: nonnegative with total weight one) and a table `q`. Here `q_{xy}` and `ℓ_{xy}`
are the outcome distributions `(a, b) ↦ q(a,b|x,y)` and `(a, b) ↦ ℓ(a,b|x,y)` of the context
`(x, y)`. The minimum over the local set `C_d` is written as an infimum. -/
def statStrength {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (μ : Fin 2 → Fin 2 → ℝ) (q : Table α β) : ℝ≥0∞ :=
  ⨅ ℓ ∈ localSet α β, ∑ x, ∑ y, ENNReal.ofReal (μ x y) *
    relEntropy (fun z : α × β => q x y z.1 z.2) (fun z : α × β => ℓ x y z.1 z.2)

end

end OQP27

-- Copied from `CGLMPBounds/Defs/TensorMeasurement.lean`, namespace `CGLMPBounds` renamed to `OQP27`.

namespace OQP27.TensorCHSH

open Matrix

noncomputable section

/-- Pauli `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Pauli `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Single-pair observables in the tracial order `t = 0, 1, 2, 3`:
`Z`, `(Z + X)/√2`, `X`, `(Z - X)/√2`. Only `t ≤ 3` is used. -/
def chshObservable : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => pauliZ
  | 1 => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (pauliZ + pauliX)
  | 2 => pauliX
  | _ => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (pauliZ - pauliX)

/-- Projector onto the `(-1)^c` eigenspace of the single-pair observable: `(1 + (-1)^c O)/2`. -/
def qubitProjector (t : ℕ) (c : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + (if c then (-1 : ℂ) else 1) • chshObservable t)

/-- The common-setting tensor product `⊗_j P_{a_j}` on `(ℂ²)^{⊗m}`. -/
def tensorProjector (m t : ℕ) (a : Fin m → Bool) : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  Matrix.of fun s s' => ∏ j, qubitProjector t (a j) (s j) (s' j)

/-- The same projector on `ℂ^{2^m}`. -/
def tensorProjectorFin (m t : ℕ) (a : Fin m → Bool) : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
  Matrix.reindex finFunctionFinEquiv finFunctionFinEquiv (tensorProjector m t a)

/-- The common-input tensor CHSH behaviour `T_m` of (F.5) on `Φ_{2^m}`: Alice's tracial
measurements `P^{2x}` and Bob's `P^{1+2y}`. -/
def tensorCHSHTable (m : ℕ) : Table (Fin m → Bool) (Fin m → Bool) :=
  tracialTable (fun x a => tensorProjectorFin m (2 * x.val) a)
    (fun y b => tensorProjectorFin m (1 + 2 * y.val) b)

end

end OQP27.TensorCHSH

-- Copied from `CGLMPBounds/Defs/QuantumGeneral.lean`, namespace `CGLMPBounds` renamed to `OQP27`.

section QuantumGeneral

open scoped ComplexOrder Kronecker

namespace OQP27

/-- A positive operator-valued measure on `ℂᵐ` with outcomes in `α`: positive semidefinite elements
summing to the identity. -/
structure IsPOVM {m : ℕ} {α : Type*} [Fintype α] (E : α → Matrix (Fin m) (Fin m) ℂ) : Prop where
  /-- Each element is positive semidefinite. -/
  posSemidef : ∀ a, (E a).PosSemidef
  /-- The elements sum to the identity. -/
  sum_eq_one : ∑ a, E a = 1

/-- A density matrix (quantum state): positive semidefinite with unit trace. -/
structure IsDensityMatrix {ι : Type*} [Fintype ι] (ρ : Matrix ι ι ℂ) : Prop where
  /-- The matrix is positive semidefinite. -/
  posSemidef : ρ.PosSemidef
  /-- The trace is one. -/
  trace_eq_one : ρ.trace = 1

noncomputable section

/-- The behaviour `q(a,b|x,y) = Re Tr(ρ (E_x(a) ⊗ F_y(b)))` of a state `ρ` on `ℂ^{dA} ⊗ ℂ^{dB}` with
Alice's measurements `E x` and Bob's measurements `F y`. For positive semidefinite factors the trace
is real; `Re` only fixes the type. -/
def quantumTable {α β : Type*} {dA dB : ℕ} (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (E : Fin 2 → α → Matrix (Fin dA) (Fin dA) ℂ) (F : Fin 2 → β → Matrix (Fin dB) (Fin dB) ℂ) :
    Table α β :=
  fun x y a b => (Matrix.trace (ρ * (E x a ⊗ₖ F y b))).re

/-- The behaviours of finite-dimensional quantum states and finite-outcome POVMs, with outcomes in
`α` for Alice and `β` for Bob (all local dimensions `dA, dB`). -/
def quantumBehaviours (α β : Type*) [Fintype α] [Fintype β] : Set (Table α β) :=
  {q | ∃ (dA dB : ℕ) (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
      (E : Fin 2 → α → Matrix (Fin dA) (Fin dA) ℂ) (F : Fin 2 → β → Matrix (Fin dB) (Fin dB) ℂ),
      IsDensityMatrix ρ ∧ (∀ x, IsPOVM (E x)) ∧ (∀ y, IsPOVM (F y)) ∧ q = quantumTable ρ E F}

/-- The maximally entangled vector `|Φ_d⟩ = d^{-1/2} Σ_j |jj⟩` in `ℂ^d ⊗ ℂ^d`. -/
def phiVec (d : ℕ) : Fin d × Fin d → ℂ :=
  fun p => if p.1 = p.2 then ((Real.sqrt d)⁻¹ : ℝ) else 0

/-- The maximally entangled state `|Φ_d⟩⟨Φ_d|`. -/
def phiState (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.vecMulVec (phiVec d) (star (phiVec d))

end

end OQP27

end QuantumGeneral

-- Copied from `CGLMPBounds/Defs/BGP.lean`, namespace `CGLMPBounds` renamed to `OQP27`;
-- the bound in `bgpIndex` is proved by a term instead of `omega` (same function).

namespace OQP27

/-- The marginal coefficients `ℓ = (−1, −1, 0, −1, 0, 0)` of (G.1). Entry `3x + a` multiplies Alice's
marginal `pA(a|x)` in `ℓ · pA`, and Bob's marginal `pB(a|x)` in `ℓ · pB`. -/
def bgpL : Fin 6 → ℤ := ![-1, -1, 0, -1, 0, 0]

/-- The joint coefficients `H` of (G.1), row by row. Entry `(3x + a, 3y + b)` multiplies
`p(a, b|x, y)`. -/
def bgpH : Fin 6 → Fin 6 → ℤ :=
  ![![0, 1, 0, 1, 0, 1],
    ![1, 0, 0, 1, 1, 0],
    ![0, 0, -1, 1, 0, 0],
    ![1, 1, 1, 1, 0, 0],
    ![0, 1, 0, 0, 0, -1],
    ![1, 0, 0, 0, -1, 0]]

/-- The coordinate index `3x + a` of input `x ∈ {0, 1}` and outcome `a ∈ {0, 1, 2}`. -/
def bgpIndex (x : Fin 2) (a : Fin 3) : Fin 6 :=
  ⟨3 * x.val + a.val,
    Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.mul_le_mul_left 3 (Nat.le_of_lt_succ x.isLt))
      (Nat.le_of_lt_succ a.isLt)) (Nat.lt_succ_self 5)⟩

noncomputable section

/-- The functional `F(p) = ℓ · pA + ℓ · pB + Σ_{x,y} Σ_{a,b<3} H_{3x+a,3y+b} p(a,b|x,y)` of (G.1),
for four outcomes per party. Alice's marginal is read in the context `(x, 0)` and Bob's in the
context `(0, y)` (see the module docstring). -/
def bgpFunctional (p : Table (Fin 4) (Fin 4)) : ℝ :=
  (∑ x : Fin 2, ∑ a : Fin 3, (bgpL (bgpIndex x a) : ℝ) * ∑ b, p x 0 a.castSucc b)
    + (∑ y : Fin 2, ∑ b : Fin 3, (bgpL (bgpIndex y b) : ℝ) * ∑ a, p 0 y a b.castSucc)
    + ∑ x : Fin 2, ∑ y : Fin 2, ∑ a : Fin 3, ∑ b : Fin 3,
        (bgpH (bgpIndex x a) (bgpIndex y b) : ℝ) * p x y a.castSucc b.castSucc

end

end OQP27

section Statements

open scoped Matrix Kronecker

/-! ## Problem 27.B -/

/-- **OQP 27.B, first claim: true for projective measurements.** "Numerically, the observables
maximally violating the CGLMP inequality on a maximally entangled state are of a very specific form,
involving measurements in computational basis, transformed by only discrete Fourier transformation
and diagonal unitaries. Show that this is necessarily the case."

Let `d ≥ 2` and `n ≥ 1`, and let `P 0, P 1, P 2, P 3` be projective measurements on `ℂⁿ` with
outcomes in `ZMod d`, in the tracial form `(A₀ᵀ, B₀, A₁ᵀ, B₁)` of a strategy on `Φ_n`. Then the CGLMP
value is at most `I_d^F = cglmpFourierValue d`, and it equals `I_d^F` exactly when `n = d k` and,
after one common unitary change of basis, `P t a` is the Fourier-phase projector
`fourierProjector d t a` tensored with the identity of `ℂᵏ`. For `n = d` (`k = 1`) the maximal
violators are exactly the rank-one Fourier-phase measurements up to a common unitary.
`OQP27.fourier_attains_cglmp_value` shows that the value `I_d^F > 2` is attained. This is Theorem
A.1 of the paper of record. -/
theorem OQP27.partB_maximizers_are_fourier_phase {d n : ℕ} [NeZero d] [NeZero n] (hd : 2 ≤ d)
    (P : Fin 4 → ZMod d → Matrix (Fin n) (Fin n) ℂ) (hP : ∀ t, OQP27.IsPVM (P t)) :
    OQP27.cglmp d (OQP27.tracialTable ![P 0, P 2] ![P 1, P 3])
        ≤ OQP27.cglmpFourierValue d ∧
      (OQP27.cglmp d (OQP27.tracialTable ![P 0, P 2] ![P 1, P 3])
          = OQP27.cglmpFourierValue d ↔
        ∃ (k : ℕ) (U : Matrix (Fin n) (Fin d × Fin k) ℂ),
          n = d * k ∧ U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
          ∀ (t : Fin 4) (a : ZMod d), P t a =
            U * (OQP27.fourierProjector d t.val a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) * Uᴴ) := by
  sorry

/-- **OQP 27.B, second claim: false in the global white-noise sense** (true for the threshold of the
CGLMP witness, `OQP27.cglmp_witness_tolerance`). "Show also that these measurements realize the highest
resistance of violation to noise."

For every `m ≥ 955`, the tensor-CHSH behaviour `T_m` has strictly smaller critical visibility under
uniform (white) noise than the Fourier-phase behaviour `Q_{2^m}`: it tolerates more noise. Both live
on the maximally entangled state of local dimension `2^m`, with two settings and `2^m` outcomes per
party and complete rank-one projective measurements (`OQP27.tensor_chsh_rank_one_pvm` for `T_m`;
`OQP27.fourier_projectors_pvm` for `Q_{2^m}`, whose elements project onto single vectors). This is
equation (A.6) of the paper of record; the explicit separating constant is in
`OQP27.noise_separation_955`. For the threshold of the CGLMP witness itself the Fourier family is
optimal (`OQP27.cglmp_witness_tolerance`). -/
theorem OQP27.partB_noise_resistance_not_optimal (m : ℕ) (hm : 955 ≤ m) :
    OQP27.critVisibility (OQP27.TensorCHSH.tensorCHSHTable m)
      < OQP27.critVisibility (OQP27.fourierTable (2 ^ m)) := by
  sorry

/-- **OQP 27.B, third claim: false.** "Show also that these measurements realize ... the best
discrimination against classical realism in the sense of Kullback–Leibler divergence."

For every `m ≥ 41`, the statistical strength (Kullback–Leibler divergence from the local polytope, in
bits per trial) of the tensor-CHSH behaviour `T_m` with uniform inputs is strictly larger than that
of the Fourier-phase behaviour `Q_{2^m}` with its best input law. This is equation (F.16) of the
paper of record; the explicit constants are in `OQP27.statistical_separation`. -/
theorem OQP27.partB_kl_discrimination_not_optimal (m : ℕ) (hm : 41 ≤ m) :
    (⨆ μ ∈ {μ : Fin 2 → Fin 2 → ℝ | (∀ x y, 0 ≤ μ x y) ∧ ∑ x, ∑ y, μ x y = 1},
        OQP27.statStrength μ (OQP27.fourierTable (2 ^ m)))
      < OQP27.statStrength (fun _ _ => 1 / 4) (OQP27.TensorCHSH.tensorCHSHTable m) := by
  sorry

/-! ## Statements of the paper of record behind the answers to 27.B, and sanity checks -/

/-- The CGLMP inequality: for `d ≥ 2`, every local behaviour `q` satisfies `I_d(q) ≤ 2`, and the bound
is attained by a local behaviour. With `OQP27.fourier_attains_cglmp_value` (`I_d^F > 2`) this shows that
`cglmp` is a Bell functional with local bound `2` that projective measurements on maximally entangled
states violate. -/
theorem OQP27.cglmp_local_bound (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ q ∈ OQP27.localSet (ZMod d) (ZMod d), OQP27.cglmp d q ≤ 2) ∧
      ∃ q ∈ OQP27.localSet (ZMod d) (ZMod d), OQP27.cglmp d q = 2 := by
  sorry

/-- Theorem A.1 (attainment) and (A.5) of the paper of record: the Fourier-phase measurements on
`Φ_d` attain the projective value, `I_d(Q_d) = I_d^F = 4/(d(d - 1)) Σ_{h=1}^{d-1} (d - h) sec(πh/(2d))`,
with `I_d^F > 2`; consequently the uniform-noise mixture `v Q_d + (1 - v) u_d` violates the CGLMP
inequality exactly when `v > 2/I_d^F`. (Non-vacuity of `OQP27.partB_maximizers_are_fourier_phase`.) -/
theorem OQP27.fourier_attains_cglmp_value (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    OQP27.cglmp d (OQP27.fourierTable d) = OQP27.cglmpFourierValue d ∧
      2 < OQP27.cglmpFourierValue d ∧
      ∀ v : ℝ, 2 < OQP27.cglmp d (OQP27.noisy v (OQP27.fourierTable d))
        ↔ 2 / OQP27.cglmpFourierValue d < v := by
  sorry

/-- (B.2) of the paper of record: for every `d ≥ 1` and phase index `t`, the Fourier-phase projectors
`Π^t_a = |ψ_{t,a}⟩⟨ψ_{t,a}|`, `a ∈ ZMod d`, form a projective measurement (each is Hermitian and
idempotent, and they sum to the identity). -/
theorem OQP27.fourier_projectors_pvm (d : ℕ) [NeZero d] (t : ℕ) :
    OQP27.IsPVM (OQP27.fourierProjector d t) := by
  sorry

/-- The tracial form of projective strategies on `Φ_n` (Appendix B of the paper of record). For all
`n × n` matrices `A x a` and `B y b`:
- `|Φ_n⟩⟨Φ_n|` is a density matrix;
- the behaviour of `|Φ_n⟩⟨Φ_n|` with Alice's measurement elements `(A x a)ᵀ` and Bob's `B y b` is
  the tracial table `q(a, b|x, y) = n⁻¹ Re Tr(A_{x,a} B_{y,b})`;
- if the `A x` and `B y` are PVMs, then so are Alice's physical measurements `a ↦ (A x a)ᵀ`, and the
  tracial table is a finite-dimensional quantum behaviour. -/
theorem OQP27.tracial_table_physical (n : ℕ) [NeZero n] {α β : Type*} [Fintype α] [Fintype β]
    (A : Fin 2 → α → Matrix (Fin n) (Fin n) ℂ) (B : Fin 2 → β → Matrix (Fin n) (Fin n) ℂ) :
    OQP27.IsDensityMatrix (OQP27.phiState n) ∧
      OQP27.quantumTable (OQP27.phiState n) (fun x a => Matrix.transpose (A x a)) B
        = OQP27.tracialTable A B ∧
      ((∀ x, OQP27.IsPVM (A x)) → (∀ y, OQP27.IsPVM (B y)) →
        (∀ x, OQP27.IsPVM (fun a => Matrix.transpose (A x a))) ∧
          OQP27.tracialTable A B ∈ OQP27.quantumBehaviours α β) := by
  sorry

/-- Appendix F.2 of the paper of record: the four tracial settings `(A₀ᵀ, B₀, A₁ᵀ, B₁)` of the
tensor-CHSH strategy `T_m` are complete rank-one projective measurements on `ℂ^(2^m)`, with every
`m`-bit outcome kept: each is a PVM, and every element has trace one and rank one. -/
theorem OQP27.tensor_chsh_rank_one_pvm (m : ℕ) (t : Fin 4) :
    OQP27.IsPVM (OQP27.TensorCHSH.tensorProjectorFin m t.val) ∧
      (∀ a : Fin m → Bool,
        Matrix.trace (OQP27.TensorCHSH.tensorProjectorFin m t.val a) = (1 : ℂ)) ∧
      ∀ a : Fin m → Bool,
        (OQP27.TensorCHSH.tensorProjectorFin m t.val a).rank = 1 := by
  sorry

/-- (A.5) of the paper of record, the CGLMP-witness threshold: for projective strategies on `Φ_n`
that violate the CGLMP inequality, the uniform-noise mixture keeps violating it exactly above the
visibility `2/I_d(q)`; this threshold is never below `2/I_d^F`, and it equals `2/I_d^F` exactly for
the (amplified) Fourier-phase measurements. In this sense the Fourier family does realize the
highest noise resistance of the CGLMP violation itself. -/
theorem OQP27.cglmp_witness_tolerance {d n : ℕ} [NeZero d] [NeZero n] (hd : 2 ≤ d)
    (P : Fin 4 → ZMod d → Matrix (Fin n) (Fin n) ℂ) (hP : ∀ t, OQP27.IsPVM (P t))
    (hviolation : 2 < OQP27.cglmp d (OQP27.tracialTable ![P 0, P 2] ![P 1, P 3])) :
    let q := OQP27.tracialTable ![P 0, P 2] ![P 1, P 3]
    (∀ v : ℝ, 2 < OQP27.cglmp d (OQP27.noisy v q) ↔ 2 / OQP27.cglmp d q < v) ∧
    2 / OQP27.cglmpFourierValue d ≤ 2 / OQP27.cglmp d q ∧
    (2 / OQP27.cglmp d q = 2 / OQP27.cglmpFourierValue d ↔
      ∃ (k : ℕ) (U : Matrix (Fin n) (Fin d × Fin k) ℂ),
        n = d * k ∧ U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
        ∀ (t : Fin 4) (a : ZMod d), P t a =
          U * (OQP27.fourierProjector d t.val a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) * Uᴴ) := by
  sorry

/-- Equation (A.6) of the paper of record: for every integer `m ≥ 955`, the tensor-CHSH behaviour
`T_m` and the Fourier-phase behaviour `Q_{2^m}`, both on `Φ_{2^m}` with two settings and `2^m`
outcomes per party, satisfy `v_crit(T_m) < 3049/5000 < v_crit(Q_{2^m})` (global critical
visibility under uniform noise). -/
theorem OQP27.noise_separation_955 (m : ℕ) (hm : 955 ≤ m) :
    OQP27.critVisibility (OQP27.TensorCHSH.tensorCHSHTable m) < 3049 / 5000 ∧
      (3049 : ℝ) / 5000 < OQP27.critVisibility (OQP27.fourierTable (2 ^ m)) := by
  sorry

/-- Equation (F.16) of the paper of record: for every `m ≥ 41`, the tensor-CHSH behaviour `T_m`
with uniform inputs and the Fourier-phase behaviour `Q_{2^m}`, both on `Φ_{2^m}`, satisfy
`S_unif(T_m) > (9/14) log₂(4/3) > (16/25) log₂(4/3) > sup_μ S_μ(Q_{2^m})`, where `μ` ranges over
input laws (probability distributions on the four input pairs). -/
theorem OQP27.statistical_separation (m : ℕ) (hm : 41 ≤ m) :
    ENNReal.ofReal (9 / 14 * Real.logb 2 (4 / 3))
        < OQP27.statStrength (fun _ _ => 1 / 4) (OQP27.TensorCHSH.tensorCHSHTable m) ∧
      (16 / 25 : ℝ) * Real.logb 2 (4 / 3) < 9 / 14 * Real.logb 2 (4 / 3) ∧
      (⨆ μ ∈ {μ : Fin 2 → Fin 2 → ℝ | (∀ x y, 0 ≤ μ x y) ∧ ∑ x, ∑ y, μ x y = 1},
          OQP27.statStrength μ (OQP27.fourierTable (2 ^ m)))
        < ENNReal.ofReal (16 / 25 * Real.logb 2 (4 / 3)) := by
  sorry

/-! ## Problem 27.A: the Bancal–Gisin–Pironio facet (a re-certification of their 2010 result)

"Show that every face of the local polytope C, which is not already contained in a face of the
no-signalling polytope P is of CGLMP type, i.e., an inequality of the form first written out in
[CGLMP], but possibly lifted from lower dimensions by fusing together some outcomes."

For `(N, M, K) = (2, 2, 4)` the inequality `F ≤ 0` of Bancal, Gisin and Pironio, with `F` the
functional `bgpFunctional` (equation (G.1) of the paper of record), is a facet of `C₄`
(`OQP27.bgp_facet`); its saturation face meets the relative interior of the no-signalling polytope,
so it is not contained in a face of `P` (`OQP27.bgp_relative_interior_point`), and some
no-signalling behaviour violates it (`OQP27.bgp_no_signalling_violation`); it is not the CGLMP₄
facet up to any relabelling (`OQP27.bgp_not_cglmp_four`); and it is not lifted from fewer outcomes
by fusing outcomes (`OQP27.bgp_no_fusion`). The last two theorems exclude the two readings of "of
CGLMP type". A facet is in particular a face, so the literal wording "every face" is answered as
well. -/

/-- Proposition G.1 ("Inequality (G.1) defines a facet of `C₄`"), with the rank statement of its
proof: the local polytope `C₄` has affine dimension `48`, the saturation face `C₄ ∩ {F = 0}` has
affine dimension `47`, and `F ≤ 0` on `C₄`. Hence (G.1) is valid on `C₄` and its saturation face has
codimension one, i.e. it is a facet. -/
theorem OQP27.bgp_facet :
    Module.finrank ℝ (vectorSpan ℝ (OQP27.localSet (Fin 4) (Fin 4))) = 48 ∧
      Module.finrank ℝ (vectorSpan ℝ (OQP27.localSet (Fin 4) (Fin 4) ∩
        {q | OQP27.bgpFunctional q = 0})) = 47 ∧
      ∀ q ∈ OQP27.localSet (Fin 4) (Fin 4), OQP27.bgpFunctional q ≤ 0 := by
  sorry

/-- Proof of Proposition G.1 ("meeting the relative interior of `P₄`"): the average
`p̄ = (1/72) Σ_{s ∈ S} q_s` of the deterministic tables of the saturating strategies
`S = {s : F(q_s) = 0}` is a local behaviour with `F(p̄) = 0`. It is no-signalling, its minimum entry
is `1/72`, and it lies in the relative interior of the no-signalling polytope `P₄`. -/
theorem OQP27.bgp_relative_interior_point (pbar : OQP27.Table (Fin 4) (Fin 4))
    (hpbar : pbar = (1 / 72 : ℝ) • ∑ s ∈ Finset.univ.filter
      (fun s : OQP27.Strategy (Fin 4) (Fin 4) =>
        OQP27.bgpFunctional (OQP27.detTable s) = 0), OQP27.detTable s) :
    pbar ∈ OQP27.localSet (Fin 4) (Fin 4) ∧ OQP27.bgpFunctional pbar = 0 ∧
      OQP27.IsNoSignalling pbar ∧ (∀ x y a b, 1 / 72 ≤ pbar x y a b) ∧
      (∃ x y a b, pbar x y a b = 1 / 72) ∧
      pbar ∈ intrinsicInterior ℝ
        {q : OQP27.Table (Fin 4) (Fin 4) | OQP27.IsNoSignalling q} := by
  sorry

/-- Proposition G.1: there is a rational no-signalling behaviour `p⁺` with `F(p⁺) = 1/144`. -/
theorem OQP27.bgp_no_signalling_violation :
    ∃ p : OQP27.Table (Fin 4) (Fin 4), OQP27.IsNoSignalling p ∧
      (∀ x y a b, ∃ r : ℚ, p x y a b = r) ∧ OQP27.bgpFunctional p = 1 / 144 := by
  sorry

/-- Proposition G.1, distinction from CGLMP₄: no bijection of deterministic strategies preserves the
two saturation predicates (the library's proof counts the saturating strategies: 72 for `F`, 80 for
CGLMP₄). In particular, no relabelling of settings, outcomes or parties takes this facet to the CGLMP₄
facet; such relabellings induce bijections. -/
theorem OQP27.bgp_not_cglmp_four :
    ¬ ∃ e : OQP27.Strategy (Fin 4) (Fin 4) ≃
        OQP27.Strategy (ZMod 4) (ZMod 4),
      ∀ s, OQP27.bgpFunctional (OQP27.detTable s) = 0 ↔
        OQP27.cglmp 4 (OQP27.detTable (e s)) = 2 := by
  sorry

/-- Proposition G.1, exclusion of outcome-fusion liftings. For every pair of outcome maps (allowed
to depend on the local setting), if either map identifies two outcomes in some setting, the BGP
functional cannot factor through their joint map on deterministic strategies. The target outcome
types and target functional are arbitrary, so this also excludes positive rescalings, affine shifts
and additions of no-signalling identities to fusion liftings. -/
theorem OQP27.bgp_no_fusion {α β : Type*}
    (fA : Fin 2 → Fin 4 → α) (fB : Fin 2 → Fin 4 → β)
    (hf : (∃ x, ¬ Function.Injective (fA x)) ∨ (∃ y, ¬ Function.Injective (fB y))) :
    ¬ ∃ G : OQP27.Strategy α β → ℝ,
      ∀ s : OQP27.Strategy (Fin 4) (Fin 4),
        OQP27.bgpFunctional (OQP27.detTable s) =
          G (fun x => fA x (s.1 x), fun y => fB y (s.2 y)) := by
  sorry

end Statements
