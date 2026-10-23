module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Data.List.Enum
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.WithTopology

@[expose] public section

/-!
# Three-copy nondistillability of the qutrit Werner state: statement of record

This file imports only Mathlib. It repeats verbatim the definitions of
`ThreeCopyQutritWerner/Basic.lean` (the block between the `verbatim` markers below) and states the
results proved in `Solution.lean`, each with `sorry` here. `comparator.json` lists these theorems,
with the permitted axioms `propext`, `Classical.choice` and `Quot.sound`, for Lean's Comparator.

Theorem, equation and section numbers below refer to the manuscript formalized here (see
`paper/README.md`). The statements concern the qutrit case `d = 3` (three copies), except where a
statement says otherwise.

* `qutritEndpointInequality` (Theorem 2.1 at `α = 1/2`, claim T2.1a): `q(C) ≥ 0` for every complex
  `27 × 27` matrix of rank at most two.
* `sharp_minimum`, `interior_minimizers` (Theorem 2.1, eqs. (4) and (5)),
  `minimum_formula_unequal_dims` (Theorem 2.1, unequal dimensions, the case `2 ≤ dᵢ ≤ 3`)
  and `werner_three_three_copy_iff`, `werner_three_npt_not_three_copy`, `overlap_le_half`
  (Corollary 2.2): the manuscript's consequences of the endpoint inequality.
* The remaining theorems are the further results of Sections 1-6 and Appendices A-C that the
  formalization proves (identities, the PPT region, attainment, the zero families of Theorem 5.1,
  the implications from T2.1a, and the reduction of T2.1a to an exact certificate).

Conventions: "distillable" is the local-filter notion (`IsOneCopyFilterDistillable`,
`IsThreeCopyFilterDistillable`: some local filters with two-dimensional outputs on each side map
one, respectively three, copies to an NPT two-qubit operator); the overlap claim of Corollary 2.2 is
stated for trace-preserving separable operations (`sepOutput`).
-/

-- verbatim: ThreeCopyQutritWerner/Basic.lean
noncomputable section

open scoped BigOperators ComplexOrder

namespace ThreeCopyQutritWerner

/-- Squared Frobenius (Hilbert–Schmidt) norm `‖M‖_F² = ∑ᵢⱼ |Mᵢⱼ|²`. -/
def frobSq {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

section Invariants

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- Unnormalized partial trace over site 1. -/
def ptrace₁ (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix (b × c) (b × c) ℂ :=
  fun y y' => ∑ i, C (i, y) (i, y')

/-- Unnormalized partial trace over site 2. -/
def ptrace₂ (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix (a × c) (a × c) ℂ :=
  fun x x' => ∑ j, C (x.1, j, x.2) (x'.1, j, x'.2)

/-- Unnormalized partial trace over site 3. -/
def ptrace₃ (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix (a × b) (a × b) ℂ :=
  fun x x' => ∑ k, C (x.1, x.2, k) (x'.1, x'.2, k)

/-- Unnormalized partial trace over sites 1 and 2. -/
def ptrace₁₂ (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix c c ℂ :=
  fun k k' => ∑ i, ∑ j, C (i, j, k) (i, j, k')

/-- Unnormalized partial trace over sites 1 and 3. -/
def ptrace₁₃ (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix b b ℂ :=
  fun j j' => ∑ i, ∑ k, C (i, j, k) (i, j', k)

/-- Unnormalized partial trace over sites 2 and 3. -/
def ptrace₂₃ (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix a a ℂ :=
  fun i i' => ∑ j, ∑ k, C (i, j, k) (i', j, k)

/-- `N = ‖C‖_F²` (manuscript eq. (2)). -/
def invN (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ := frobSq C

/-- `A = ∑ᵢ ‖Trᵢ C‖_F²` (manuscript eq. (2)). -/
def invA (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  frobSq (ptrace₁ C) + frobSq (ptrace₂ C) + frobSq (ptrace₃ C)

/-- `B = ∑_{i<j} ‖Tr_{ij} C‖_F²` (manuscript eq. (2)). -/
def invB (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  frobSq (ptrace₁₂ C) + frobSq (ptrace₁₃ C) + frobSq (ptrace₂₃ C)

/-- `T₀ = |Tr C|²` (manuscript eq. (2)). -/
def invT (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ := Complex.normSq C.trace

/-- `q_α(C) = N - α A + α² B - α³ T₀` (manuscript eq. (3)). -/
def energy (α : ℝ) (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  invN C - α * invA C + α ^ 2 * invB C - α ^ 3 * invT C

/-- The endpoint form `q(C) = q_{1/2}(C)` (manuscript eq. (3)). -/
def endpointEnergy (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ := energy (1 / 2) C

/-- `R(C) = N - T₀ / 2` (manuscript eq. (7)). -/
def formR (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ := invN C - invT C / 2

/-- `S(C) = N - (A + B) / 6 + T₀ / 4` (manuscript eq. (7)). -/
def formS (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  invN C - (invA C + invB C) / 6 + invT C / 4

/-- Grouped two-factor form at the cut `1 | 23` (manuscript eq. (8), `i = 1`). -/
def cutForm₁ (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  invN C - (frobSq (ptrace₁ C) + frobSq (ptrace₂₃ C)) / 2 + invT C / 4

/-- Grouped two-factor form at the cut `2 | 13` (manuscript eq. (8), `i = 2`). -/
def cutForm₂ (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  invN C - (frobSq (ptrace₂ C) + frobSq (ptrace₁₃ C)) / 2 + invT C / 4

/-- Grouped two-factor form at the cut `3 | 12` (manuscript eq. (8), `i = 3`). -/
def cutForm₃ (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  invN C - (frobSq (ptrace₃ C) + frobSq (ptrace₁₂ C)) / 2 + invT C / 4

/-- Three-site tensor product `M₁ ⊗ M₂ ⊗ M₃`. -/
def tensor₃ (M₁ : Matrix a a ℂ) (M₂ : Matrix b b ℂ) (M₃ : Matrix c c ℂ) :
    Matrix (a × b × c) (a × b × c) ℂ :=
  fun x y => M₁ x.1 y.1 * M₂ x.2.1 y.2.1 * M₃ x.2.2 y.2.2

end Invariants

/-- The sharp curve `f(α) = (1 - 2α)(1 - α)²` (manuscript eq. (4)). -/
def sharpCurve (α : ℝ) : ℝ := (1 - 2 * α) * (1 - α) ^ 2

section Werner

/-- The flip operator `F (u ⊗ v) = v ⊗ u` on two copies of `ℂ^d`. -/
def swapOp (d : Type*) [DecidableEq d] : Matrix (d × d) (d × d) ℂ :=
  fun x y => if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0

/-- The unnormalized projector `Ω = |Ω⟩⟨Ω|`, where `|Ω⟩ = ∑ⱼ |jj⟩`. -/
def omegaOp (d : Type*) [DecidableEq d] : Matrix (d × d) (d × d) ℂ :=
  fun x y => if x.1 = x.2 ∧ y.1 = y.2 then 1 else 0

/-- Partial transpose on the second tensor factor. -/
def partialTranspose {m n : Type*} (M : Matrix (m × n) (m × n) ℂ) :
    Matrix (m × n) (m × n) ℂ :=
  fun x y => M (x.1, y.2) (y.1, x.2)

/-- The Werner state `ρ_{d,α} = (I - α F_d) / (d (d - α))` (manuscript eq. (1)).
The manuscript's parameter range is `-1 ≤ α ≤ 1`; the definition is total. -/
def werner (d : ℕ) (α : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) •
    ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - (α : ℂ) • swapOp (Fin d))

/-- Three tensor copies `M ⊗ M ⊗ M` of a bipartite operator on `A ⊗ B`,
regrouped along the cut `A₁A₂A₃ | B₁B₂B₃`. -/
def tripleCopy {m n : Type*} (M : Matrix (m × n) (m × n) ℂ) :
    Matrix ((m × m × m) × (n × n × n)) ((m × m × m) × (n × n × n)) ℂ :=
  fun x y =>
    M (x.1.1, x.2.1) (y.1.1, y.2.1) * M (x.1.2.1, x.2.2.1) (y.1.2.1, y.2.2.1) *
      M (x.1.2.2, x.2.2.2) (y.1.2.2, y.2.2.2)

/-- Row-first vectorization of a coefficient matrix: `(vec C) (x, y) = C x y`. -/
def vec {A B : Type*} (C : Matrix A B ℂ) : A × B → ℂ := fun p => C p.1 p.2

/-- The sesquilinear expectation `⟨ψ, M ψ⟩ = ∑ₓᵧ conj(ψ x) M x y ψ y`. -/
def expectation {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℂ :=
  ∑ x, ∑ y, star (ψ x) * M x y * ψ y

/-- `ψ` is a sum of at most `r` product vectors across the cut `A | B`,
i.e. it has Schmidt rank at most `r`. -/
def SchmidtRankLE {A B : Type*} (r : ℕ) (ψ : A × B → ℂ) : Prop :=
  ∃ (u : Fin r → A → ℂ) (v : Fin r → B → ℂ), ∀ x y, ψ (x, y) = ∑ k, u k x * v k y

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A bipartite operator has negative partial transpose (is NPT) when its
partial transpose is not positive semidefinite. -/
def IsNPT (ρ : Matrix (m × n) (m × n) ℂ) : Prop :=
  ¬ (partialTranspose ρ).PosSemidef

/-- One-copy Schmidt-rank-two detection: some vector of Schmidt rank at most two has
negative expectation in `ρ^Γ`.  This is the criterion, not the operational notion;
`IsOneCopyFilterDistillable` below is the operational notion, and the two are proved
equivalent for Hermitian `ρ` in `Distillation.lean`. -/
def IsOneCopyRankTwoDetectable (ρ : Matrix (m × n) (m × n) ℂ) : Prop :=
  ∃ ψ : m × n → ℂ, SchmidtRankLE 2 ψ ∧ (expectation (partialTranspose ρ) ψ).re < 0

/-- Three-copy Schmidt-rank-two detection: some vector of Schmidt rank at most two across
`A₁A₂A₃ | B₁B₂B₃` has negative expectation in `(ρ^{⊗3})^Γ`.  This is the criterion;
`IsThreeCopyFilterDistillable` below is the operational notion, proved equivalent for
Hermitian `ρ` in `Distillation.lean`. -/
def IsThreeCopyRankTwoDetectable (ρ : Matrix (m × n) (m × n) ℂ) : Prop :=
  ∃ ψ : (m × m × m) × (n × n × n) → ℂ, SchmidtRankLE 2 ψ ∧
    (expectation (partialTranspose (tripleCopy ρ)) ψ).re < 0

end Werner

section StatementBase

/-! ### Further definitions used by the endpoint statements

Collected here so that the statement base contains definitions only. -/

/-- Two-site tensor product `M ⊗ N`. -/
def tensor₂ {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι ι ℂ) (N : Matrix κ κ ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ :=
  fun x y => M x.1 y.1 * N x.2 y.2

/-- Unnormalized partial trace of a two-site operator over its first site. -/
def ptraceL {b c : Type*} [Fintype b] [Fintype c] (X : Matrix (b × c) (b × c) ℂ) :
    Matrix c c ℂ :=
  fun k k' => ∑ j, X (j, k) (j, k')

/-- Unnormalized partial trace of a two-site operator over its second site. -/
def ptraceR {b c : Type*} [Fintype b] [Fintype c] (X : Matrix (b × c) (b × c) ℂ) :
    Matrix b b ℂ :=
  fun j j' => ∑ k, X (j, k) (j', k)

/-- The rank-one operator `|χ⟩⟨η|`. -/
def ketBra {ι : Type*} (χ η : ι → ℂ) : Matrix ι ι ℂ :=
  fun y y' => χ y * (starRingEnd ℂ) (η y')

/-- The inner product `⟨u, v⟩ = ∑ₓ conj(u x) v x`, conjugate-linear in the first slot. -/
def braket {ι : Type*} [Fintype ι] (u v : ι → ℂ) : ℂ :=
  ∑ x, (starRingEnd ℂ) (u x) * v x

/-- The squared norm `‖u‖² = ∑ₓ |u x|²`. -/
def vecNormSq {ι : Type*} [Fintype ι] (u : ι → ℂ) : ℝ :=
  ∑ x, Complex.normSq (u x)

/-- The locally filtered operator `(A ⊗ B) ρ (A ⊗ B)†` on two qubits. -/
def localFilter {m n : Type*} [Fintype m] [Fintype n] (A : Matrix (Fin 2) m ℂ)
    (B : Matrix (Fin 2) n ℂ) (ρ : Matrix (m × n) (m × n) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => ∑ p : m × n, ∑ q : m × n,
    A x.1 p.1 * B x.2 p.2 * ρ p q * star (A y.1 q.1) * star (B y.2 q.2)

/-- One-copy distillability, operational form: some local filter onto two
qubits yields an operator whose partial transpose is not positive semidefinite. -/
def IsOneCopyFilterDistillable {m n : Type*} [Fintype m] [Fintype n]
    (ρ : Matrix (m × n) (m × n) ℂ) : Prop :=
  ∃ (A : Matrix (Fin 2) m ℂ) (B : Matrix (Fin 2) n ℂ), IsNPT (localFilter A B ρ)

/-- Three-copy distillability, operational form: some local filter of `ρ^{⊗3}`
across `A₁A₂A₃ | B₁B₂B₃` onto two qubits yields an NPT operator. -/
def IsThreeCopyFilterDistillable {m n : Type*} [Fintype m] [Fintype n]
    (ρ : Matrix (m × n) (m × n) ℂ) : Prop :=
  ∃ (A : Matrix (Fin 2) (m × m × m) ℂ) (B : Matrix (Fin 2) (n × n × n) ℂ),
    IsNPT (localFilter A B (tripleCopy ρ))

/-- The shape of manuscript eq. (5) up to a permutation of the sites:
`C = z (P_E ⊗ |u⟩⟨u| ⊗ |v⟩⟨v|)` with `P_E = |f₁⟩⟨f₁| + |f₂⟩⟨f₂|` for an orthonormal pair,
unit vectors `u`, `v`, and `|z|² = 1/2` (that is, `z = e^{iθ}/√2`). -/
def IsInteriorMinimizerShape {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) : Prop :=
  ∃ z : ℂ, Complex.normSq z = 1 / 2 ∧
    ((∃ (f₁ f₂ : a → ℂ) (u : b → ℂ) (v : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        C = z • tensor₃ (ketBra f₁ f₁ + ketBra f₂ f₂) (ketBra u u) (ketBra v v)) ∨
      (∃ (u : a → ℂ) (f₁ f₂ : b → ℂ) (v : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        C = z • tensor₃ (ketBra u u) (ketBra f₁ f₁ + ketBra f₂ f₂) (ketBra v v)) ∨
      (∃ (u : a → ℂ) (v : b → ℂ) (f₁ f₂ : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        C = z • tensor₃ (ketBra u u) (ketBra v v) (ketBra f₁ f₁ + ketBra f₂ f₂)))

/-- `|00⟩ + |11⟩` (unnormalized); the maximally entangled state is `Φ = (|00⟩ + |11⟩)/√2`. -/
def omegaVec₂ : Fin 2 × Fin 2 → ℂ := fun x => if x.1 = x.2 then 1 else 0

/-- `Re ⟨Φ, σ Φ⟩` for `Φ = (|00⟩ + |11⟩)/√2`: the overlap of a two-qubit operator with the
maximally entangled state (real for Hermitian `σ`). -/
def maxEntOverlap (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  (expectation σ omegaVec₂).re / 2

/-- The output `Σ_k (A_k ⊗ B_k) ρ^{⊗3} (A_k ⊗ B_k)†` of a separable operation on three
copies of `ρ`, with values in two-qubit operators. -/
def sepOutput {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {K : ℕ}
    (A : Fin K → Matrix (Fin 2) (m × m × m) ℂ) (B : Fin K → Matrix (Fin 2) (n × n × n) ℂ)
    (ρ : Matrix (m × n) (m × n) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ k, localFilter (A k) (B k) (tripleCopy ρ)

/-- The qutrit endpoint inequality, manuscript Theorem 2.1 at `d = 3`, `α = 1/2`:
`q(C) ≥ 0` for every complex `27 × 27` matrix of rank at most two (claim T2.1a). -/
def QutritEndpointInequality : Prop :=
  ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
    C.rank ≤ 2 → 0 ≤ endpointEnergy C

open scoped Kronecker in
/-- A bipartite operator is separable when it is a finite nonnegative combination of tensor
products of positive semidefinite operators (used for the `d = 2` remark on Theorem 2.1). -/
def IsBipartiteSeparable {m n : Type*} [Fintype m] [Fintype n]
    (ρ : Matrix (m × n) (m × n) ℂ) : Prop :=
  ∃ (K : ℕ) (p : Fin K → ℝ) (A : Fin K → Matrix m m ℂ) (B : Fin K → Matrix n n ℂ),
    (∀ k, 0 ≤ p k) ∧ (∀ k, (A k).PosSemidef) ∧ (∀ k, (B k).PosSemidef) ∧
      ρ = ∑ k, ((p k : ℝ) : ℂ) • (A k ⊗ₖ B k)

open scoped Kronecker Matrix in
/-- `embedPair J ρ = (J ⊗ J) ρ (J ⊗ J)†` for `J : ℂ³ → ℂᵈ` (the embedding of eq. (27)). -/
def embedPair {d : ℕ} (J : Matrix (Fin d) (Fin 3) ℂ)
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (J ⊗ₖ J) * ρ * (J ⊗ₖ J)ᴴ

/-- `noisyFamily J p = p (J ⊗ J) ρ_{3,1/2} (J ⊗ J)† + (1 - p) I/d²`, the family of eq. (27) with
the qutrit seed (manuscript Corollary 6.2). -/
def noisyFamily {d : ℕ} (J : Matrix (Fin d) (Fin 3) ℂ) (p : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (p : ℂ) • embedPair J (werner 3 (1 / 2)) + (((1 - p) / (d : ℝ) ^ 2 : ℝ) : ℂ) • 1

end StatementBase

section StatementBaseRevision4

/-! Definitions for the families of Theorem 5.1 and for the certificate soundness argument of
Section 4.1. -/

open scoped Matrix Kronecker

/-- The skew matrix `[[0, 1], [-1, 0]]` of Theorem 5.1, written `ε` here. -/
def epsMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- `J₂ = ε ⊗ ε`. -/
def epsJ₂ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := epsMat ⊗ₖ epsMat

/-- `J₃ = ε ⊗ ε ⊗ ε`. -/
def epsJ₃ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  epsMat ⊗ₖ (epsMat ⊗ₖ epsMat)

/-- `B₂(U) = U ε Uᵀ J₂⁻¹ / √2` for `U : ℂ² → (ℂ²)^{⊗2}` (plain transpose). -/
def binaryB₂ (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (U * epsMat * Uᵀ * epsJ₂⁻¹)

/-- `B₃(U) = U ε Uᵀ J₃⁻¹ / √2` for `U : ℂ² → (ℂ²)^{⊗3}` (plain transpose). -/
def binaryB₃ (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (U * epsMat * Uᵀ * epsJ₃⁻¹)

/-- Family II: `|a⟩⟨b| ⊗ V B₂(U) V†` with `V = V₂ ⊗ V₃` (sites 2, 3). -/
def familyII (a b : Fin 3 → ℂ) (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ :=
  tensor₂ (ketBra a b) ((V₂ ⊗ₖ V₃) * binaryB₂ U * (V₂ ⊗ₖ V₃)ᴴ)

/-- Family III: `V B₃(U) V†` with `V = V₁ ⊗ V₂ ⊗ V₃`. -/
def familyIII (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ :=
  (V₁ ⊗ₖ (V₂ ⊗ₖ V₃)) * binaryB₃ U * (V₁ ⊗ₖ (V₂ ⊗ₖ V₃))ᴴ

/-- `(j, i, k) ↦ (i, j, k)`: the index equivalence that puts site 2 in front. -/
def siteEquiv₂ {a b c : Type*} : b × a × c ≃ a × b × c where
  toFun x := (x.2.1, x.1, x.2.2)
  invFun y := (y.2.1, y.1, y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `(k, i, j) ↦ (i, j, k)`: the index equivalence that puts site 3 in front. -/
def siteEquiv₃ {a b c : Type*} : c × a × b ≃ a × b × c where
  toFun x := (x.2.1, x.2.2, x.1)
  invFun y := (y.2.2, y.1, y.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Family I with site 1 active: `(P_E/√2) ⊗ |χ⟩⟨η|`. -/
def familyIMat (f₁ f₂ : Fin 3 → ℂ) (χ η : Fin 3 × Fin 3 → ℂ) :
    Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ :=
  tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂)) (ketBra χ η)

/-- The union of Theorem 5.1: families I and II with the active site at any of the three
positions, family III, each multiplied by a unit phase.  (Family III is closed under site
permutations through its parameters; the other site permutations of families I and II are
absorbed by `χ, η`, resp. by `U`, `V₂`, `V₃`.) -/
abbrev IsQutritZeroFamilyMember
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) : Prop :=
  ∃ z : ℂ, Complex.normSq z = 1 ∧
    ∃ D : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C = z • D ∧
      ((∃ (f₁ f₂ : Fin 3 → ℂ) (χ η : Fin 3 × Fin 3 → ℂ), vecNormSq f₁ = 1 ∧
          vecNormSq f₂ = 1 ∧ braket f₁ f₂ = 0 ∧ vecNormSq χ = 1 ∧ vecNormSq η = 1 ∧
          (D = familyIMat f₁ f₂ χ η ∨
            D = (familyIMat f₁ f₂ χ η).submatrix siteEquiv₂.symm siteEquiv₂.symm ∨
            D = (familyIMat f₁ f₂ χ η).submatrix siteEquiv₃.symm siteEquiv₃.symm)) ∨
        (∃ (a b : Fin 3 → ℂ) (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
            (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ), vecNormSq a = 1 ∧ vecNormSq b = 1 ∧
          Uᴴ * U = 1 ∧ V₂ᴴ * V₂ = 1 ∧ V₃ᴴ * V₃ = 1 ∧
          (D = familyII a b U V₂ V₃ ∨
            D = (familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm ∨
            D = (familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm)) ∨
        (∃ (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ),
          Uᴴ * U = 1 ∧ V₁ᴴ * V₁ = 1 ∧ V₂ᴴ * V₂ = 1 ∧ V₃ᴴ * V₃ = 1 ∧
          D = familyIII U V₁ V₂ V₃))

/-- The source bivector `p = (x ⊗ y - y ⊗ x)/√2` of `X = [x, y]`, as a skew matrix. -/
def bivecMat {n : Type*} [Fintype n] (X : Matrix n (Fin 2) ℂ) : Matrix n n ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (X * epsMat * Xᵀ)

/-- Transpose of the last two factors of `(r × b) × c` (the manuscript's `Γ₁₂₃₄` when `b` and
`c` are the two minor pairs). -/
def minorTranspose {r b c : Type*} (M : Matrix ((r × b) × c) ((r × b) × c) ℂ) :
    Matrix ((r × b) × c) ((r × b) × c) ℂ :=
  fun x y => M ((x.1.1, y.1.2), y.2) ((y.1.1, x.1.2), x.2)

/-- `T ⊗ I ⊗ I` on `(r × b) × c`: `T` on the first factor, the identity on `b` and `c`. -/
def liftRowCol {r b c : Type*} [DecidableEq b] [DecidableEq c] (T : Matrix r r ℂ) :
    Matrix ((r × b) × c) ((r × b) × c) ℂ :=
  fun x y => T x.1.1 y.1.1 * (1 : Matrix b b ℂ) x.1.2 y.1.2 * (1 : Matrix c c ℂ) x.2 y.2

/-- The six registers `(((row, col), (p₁, p₂)), (p₃, p₄))`, each a copy of `(ℂ³)^{⊗3}` indexed
by `Fin 3 × Fin 3 × Fin 3`. -/
abbrev SixRegisters :=
  (((Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3)) ×
    ((Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3))) ×
    ((Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3))

/-- `T = ∏ᵢ (I - Ωᵢ/2)` on `(row, col)`, as `(15/2)³ (ρ_{3,1/2}^{⊗3})^Γ`
(`ρ_{d,α}^Γ = (I - α Ω)/(d (d - α))` and `d (d - α) = 15/2`). -/
def endpointOperator :
    Matrix ((Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3))
      ((Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3)) ℂ :=
  ((15 / 2 : ℂ) ^ 3) • partialTranspose (tripleCopy (werner 3 (1 / 2)))

/-- The feature `z_h = vec C ⊗ p ⊗ p` (`P` is the bivector `p` as a matrix). -/
def featureH (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    SixRegisters → ℂ :=
  fun x => vec C x.1.1 * vec P x.1.2 * vec P x.2

/-- `T ⊗ I` on the six registers (the identity on the four minor registers). -/
def sixRegisterOperator : Matrix SixRegisters SixRegisters ℂ := liftRowCol endpointOperator

end StatementBaseRevision4

section StatementBaseRevision6

/-! Definitions for the two-factor cut forms of eq. (11). -/

/-- The grouped two-factor form of manuscript eq. (8) for an operator on `L ⊗ R`. -/
def cutForm {L R : Type*} [Fintype L] [Fintype R] (X : Matrix (L × R) (L × R) ℂ) : ℝ :=
  frobSq X - (frobSq (ptraceL X) + frobSq (ptraceR X)) / 2 + Complex.normSq X.trace / 4

/-- `‖P(X)‖² = ‖Tr_L X‖_F² + ‖Tr_R X‖_F²`. -/
def ptraceNormSq {L R : Type*} [Fintype L] [Fintype R] (X : Matrix (L × R) (L × R) ℂ) : ℝ :=
  frobSq (ptraceL X) + frobSq (ptraceR X)

/-- `e(u, v) = ‖u‖²‖v‖² + |⟨v, u⟩|² - ‖P(u v†)‖²`: four times the squared norm of `u ⊗ v` antisymmetrized
in the `L` parts and in the `R` parts of two replicas (Appendix A). -/
def biDefect {L R : Type*} [Fintype L] [Fintype R] (u v : L × R → ℂ) : ℝ :=
  vecNormSq u * vecNormSq v + Complex.normSq (braket v u) - ptraceNormSq (ketBra u v)

end StatementBaseRevision6

end ThreeCopyQutritWerner
-- end verbatim

open scoped BigOperators ComplexOrder

namespace ThreeCopyQutritWerner.Endpoints

/-! ## The endpoint inequality and its consequences in Theorem 2.1 and Corollary 2.2 -/

/-- Theorem 2.1 of the manuscript at `d = 3`, `α = 1/2` (claim T2.1a), the qutrit endpoint
inequality: `q(C) ≥ 0` for every complex `27 × 27` matrix `C` of rank at most two, where
`q = endpointEnergy` is the three-copy form `q_{1/2}` (`QutritEndpointInequality`). -/
theorem qutritEndpointInequality : QutritEndpointInequality := by
  sorry

/-- Theorem 2.1, eq. (4), at `d = 3` (claim T2.1b): for `0 ≤ α ≤ 1/2`, `q_α(C) ≥ (1 - 2α)(1 - α)² ‖C‖_F²` for
every matrix of rank at most two, with equality for some normalized matrix of rank at most two. -/
theorem sharp_minimum {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) :
    (∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank ≤ 2 →
      sharpCurve α * invN C ≤ energy α C) ∧
    ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = sharpCurve α := by
  sorry

/-- Theorem 2.1, eq. (5), at `d = 3` (claim T2.1c): for `0 < α < 1/2`, every normalized minimizer of `q_α`
over rank at most two has the shape of eq. (5) up to a permutation of the sites. -/
theorem interior_minimizers {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2)
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hC : C.rank ≤ 2) (hN : invN C = 1)
    (hmin : ∀ D : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, D.rank ≤ 2 →
      invN D = 1 → energy α C ≤ energy α D) :
    IsInteriorMinimizerShape C := by
  sorry

/-- Theorem 2.1, unequal dimensions, the case `2 ≤ dᵢ ≤ 3` (claim T2.1d): for `0 ≤ α ≤ 1/2`,
`q_α(C) ≥ (1 - 2α)(1 - α)² ‖C‖_F²` for every matrix of rank at most two on sites of dimensions
`2 ≤ dᵢ ≤ 3`, with equality for some normalized matrix of rank at most two. -/
theorem minimum_formula_unequal_dims {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] (ha2 : 2 ≤ Fintype.card a)
    (ha : Fintype.card a ≤ 3) (hb2 : 2 ≤ Fintype.card b) (hb : Fintype.card b ≤ 3)
    (hc2 : 2 ≤ Fintype.card c) (hc : Fintype.card c ≤ 3) :
    ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 / 2 →
      (∀ C : Matrix (a × b × c) (a × b × c) ℂ, C.rank ≤ 2 →
        sharpCurve α * invN C ≤ energy α C) ∧
      ∃ C : Matrix (a × b × c) (a × b × c) ℂ,
        C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = sharpCurve α := by
  sorry

/-- Corollary 2.2 at `d = 3` (claim C2.2a): for `α ≤ 1`, three copies of the qutrit Werner state are
distillable exactly when `α > 1/2`. -/
theorem werner_three_three_copy_iff {α : ℝ} (h1 : α ≤ 1) :
    IsThreeCopyFilterDistillable (werner 3 α) ↔ 1 / 2 < α := by
  sorry

/-- Corollary 2.2 at `d = 3` (claim C2.2b): for `1/3 < α ≤ 1/2` the qutrit Werner state is NPT and three
copies of it are not distillable. -/
theorem werner_three_npt_not_three_copy {α : ℝ} (h0 : 1 / 3 < α) (h1 : α ≤ 1 / 2) :
    IsNPT (werner 3 α) ∧ ¬ IsThreeCopyFilterDistillable (werner 3 α) := by
  sorry

/-- Corollary 2.2, at `d = 3` (claim C2.2c): for `0 ≤ α ≤ 1/2`, every trace-preserving
separable operation from three copies of the qutrit Werner state to two qubits outputs an operator
whose overlap with the maximally entangled state is at most `1/2`. -/
theorem overlap_le_half {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) {K : ℕ}
    (A : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (B : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (htp : ∀ u v : (Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3),
      ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
        (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) :
    maxEntOverlap (sepOutput A B (werner 3 α)) ≤ 1 / 2 := by
  sorry

/-! ## Further results of the manuscript -/

/-- Proposition 3.1, eq. (9). -/
theorem continuation_identity {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (α : ℝ) :
    energy α C - sharpCurve α * invN C =
      4 * α * (1 + α) / 3 * endpointEnergy C +
        α * (1 - 2 * α) * (2 / 3 - α) * formR C + 2 * α * (1 - 2 * α) * formS C := by
  sorry

/-- Section 3, eq. (7): R ≥ 0 on rank at most two. -/
theorem formR_nonneg_rank_two {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (h : C.rank ≤ 2) : 0 ≤ formR C := by
  sorry

/-- Section 3, eq. (8) and Appendix A: Q₁, Q₂, Q₃, S ≥ 0 on rank at most two. -/
theorem cutForms_nonneg_rank_two {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (h : C.rank ≤ 2) :
    0 ≤ cutForm₁ C ∧ 0 ≤ cutForm₂ C ∧ 0 ≤ cutForm₃ C ∧ 0 ≤ formS C := by
  sorry

/-- eq. (6), the expectation identity. -/
theorem three_copy_expectation (d : ℕ) (α : ℝ)
    (C : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ) :
    expectation (partialTranspose (tripleCopy (werner d α))) (vec C) =
      (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) ^ 3 * ((energy α C : ℝ) : ℂ) := by
  sorry

/-- eq. (6): SR(vec C) = rank C. -/
theorem schmidtRank_vec {A B : Type*} [Fintype A] [Fintype B] (C : Matrix A B ℂ) (r : ℕ) :
    SchmidtRankLE r (vec C) ↔ C.rank ≤ r := by
  sorry

/-- eq. (1): the Werner state. -/
theorem werner_state (d : ℕ) (hd : 2 ≤ d) (α : ℝ) (hm : -1 ≤ α) (h1 : α ≤ 1) :
    (werner d α).PosSemidef ∧ (werner d α).trace = 1 := by
  sorry

/-- Section 1: NPT exactly when α > 1/d. -/
theorem werner_npt_iff (d : ℕ) (hd : 2 ≤ d) (α : ℝ) (h1 : α ≤ 1) :
    IsNPT (werner d α) ↔ 1 / (d : ℝ) < α := by
  sorry

/-- Section 1: one-copy distillable exactly when α > 1/2 (d = 3). -/
theorem werner_three_one_copy_iff {α : ℝ} (hm : -1 ≤ α) (h1 : α ≤ 1) :
    IsOneCopyFilterDistillable (werner 3 α) ↔ 1 / 2 < α := by
  sorry

/-- Corollary 2.2: distillable for 1/2 < α (d = 3). -/
theorem werner_three_three_copy_of_gt {α : ℝ} (h : 1 / 2 < α) (h1 : α ≤ 1) :
    IsThreeCopyFilterDistillable (werner 3 α) := by
  sorry

/-- Corollary 2.2 proof: α ≤ 0 (d = 3). -/
theorem werner_three_not_three_copy_of_nonpos {α : ℝ} (h0 : α ≤ 0) :
    ¬ IsThreeCopyFilterDistillable (werner 3 α) := by
  sorry

/-- Corollary 2.2 at `d = 3`, PPT region: for `α ≤ 1/3` three copies are not distillable (the state
has positive partial transpose there). -/
theorem werner_three_not_three_copy_of_le_third {α : ℝ} (h : α ≤ 1 / 3) :
    ¬ IsThreeCopyFilterDistillable (werner 3 α) := by
  sorry

/-- Section 3: every matrix of the shape (5) attains the sharp curve. -/
theorem interior_shape_attains {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (h : IsInteriorMinimizerShape C) :
    C.rank ≤ 2 ∧ invN C = 1 ∧ ∀ α : ℝ, energy α C = sharpCurve α := by
  sorry

/-- eq. (21) (family I of Theorem 5.1, site 1 active): for every two-plane `E = span(f₁, f₂)`
(orthonormal pair) and unit `χ`, `η` on sites 2 and 3, `(P_E/√2) ⊗ |χ⟩⟨η|` is a normalized
endpoint zero of rank at most two, in any finite local dimensions. -/
theorem familyI_endpoint_zero_any_plane {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (f₁ f₂ : a → ℂ) (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) (h12 : braket f₁ f₂ = 0)
    (χ η : b × c → ℂ) (hχ : vecNormSq χ = 1) (hη : vecNormSq η = 1) :
    (tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)).rank ≤ 2 ∧
      invN (tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)) = 1 ∧
      endpointEnergy (tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)) = 0 := by
  sorry

/-- Section 5.1: every nonzero endpoint zero has rank two. -/
theorem endpoint_zero_rank_two {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (h : C.rank ≤ 2) (h0 : endpointEnergy C = 0)
    (hC : C ≠ 0) : C.rank = 2 := by
  sorry

/-- Corollary 2.2, separable operations, α ≤ 0 (d = 3). -/
theorem overlap_le_half_of_nonpos {α : ℝ} (h0 : α ≤ 0) {K : ℕ}
    (A : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (B : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (htp : ∀ u v : (Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3),
      ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
        (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) :
    maxEntOverlap (sepOutput A B (werner 3 α)) ≤ 1 / 2 := by
  sorry

/-- Corollary 2.2, separable operations, PPT region `α ≤ 1/3` (`d = 3`). -/
theorem overlap_le_half_of_le_third {α : ℝ} (h : α ≤ 1 / 3) {K : ℕ}
    (A : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (B : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (htp : ∀ u v : (Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3),
      ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
        (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) :
    maxEntOverlap (sepOutput A B (werner 3 α)) ≤ 1 / 2 := by
  sorry

/-- The rank-two filter criterion: for Hermitian `ρ`, one (respectively three) copies are distillable by
local filters onto two qubits exactly when some vector of Schmidt rank at most two has negative expectation in
the partial transpose of `ρ` (respectively of `ρ^{⊗3}`). -/
theorem filter_iff_rank_two_detectable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (ρ : Matrix (m × n) (m × n) ℂ) (hρ : ρ.IsHermitian) :
    (IsOneCopyFilterDistillable ρ ↔ IsOneCopyRankTwoDetectable ρ) ∧
      (IsThreeCopyFilterDistillable ρ ↔ IsThreeCopyRankTwoDetectable ρ) := by
  sorry

/-- Theorem 2.1, eq. (4), attainment (`d = 3`): for every real `α` a normalized matrix of rank at
most two attains the sharp curve. -/
theorem sharp_curve_attained (α : ℝ) :
    ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = sharpCurve α := by
  sorry

/-- Implication T2.1a ⇒ T2.1b. -/
theorem sharp_minimum_of_endpoint : QutritEndpointInequality →
    ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 / 2 →
      (∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank ≤ 2 →
        sharpCurve α * invN C ≤ energy α C) ∧
      ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
        C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = sharpCurve α := by
  sorry

/-- Implication from T2.1a: Theorem 2.1, unequal dimensions, the case `2 ≤ dᵢ ≤ 3`. -/
theorem minimum_formula_of_card_of_endpoint {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] (ha2 : 2 ≤ Fintype.card a)
    (ha : Fintype.card a ≤ 3) (hb2 : 2 ≤ Fintype.card b) (hb : Fintype.card b ≤ 3)
    (hc2 : 2 ≤ Fintype.card c) (hc : Fintype.card c ≤ 3) : QutritEndpointInequality →
    ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 / 2 →
      (∀ C : Matrix (a × b × c) (a × b × c) ℂ, C.rank ≤ 2 →
        sharpCurve α * invN C ≤ energy α C) ∧
      ∃ C : Matrix (a × b × c) (a × b × c) ℂ,
        C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = sharpCurve α := by
  sorry

/-- Implication T2.1a ⇒ T2.1c. -/
theorem interior_minimizers_of_endpoint : QutritEndpointInequality →
    ∀ {α : ℝ}, 0 < α → α < 1 / 2 →
      ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank ≤ 2 → invN C = 1 →
        (∀ D : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, D.rank ≤ 2 →
          invN D = 1 → energy α C ≤ energy α D) →
        IsInteriorMinimizerShape C := by
  sorry

/-- Implication T2.1a ⇒ C2.2a. -/
theorem werner_three_three_copy_iff_of_endpoint : QutritEndpointInequality →
    ∀ {α : ℝ}, α ≤ 1 → (IsThreeCopyFilterDistillable (werner 3 α) ↔ 1 / 2 < α) := by
  sorry

/-- Implication T2.1a ⇒ C2.2b. -/
theorem werner_three_npt_not_three_copy_of_endpoint : QutritEndpointInequality →
    ∀ {α : ℝ}, 1 / 3 < α → α ≤ 1 / 2 →
      IsNPT (werner 3 α) ∧ ¬ IsThreeCopyFilterDistillable (werner 3 α) := by
  sorry

/-- Implication T2.1a ⇒ C2.2c (separable operations). -/
theorem overlap_le_half_of_endpoint : QutritEndpointInequality →
    ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 / 2 → ∀ {K : ℕ}
      (A : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
      (B : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ),
      (∀ u v : (Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3),
        ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
          (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) →
      maxEntOverlap (sepOutput A B (werner 3 α)) ≤ 1 / 2 := by
  sorry

/-- Section 3.1, eq. (10): for a Hermitian projector `P` of trace two with `P C = C`,
`R(C) = ‖C - (Tr C) P / 2‖_F²`. -/
theorem formR_eq_proj {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C P : Matrix (a × b × c) (a × b × c) ℂ) (hP : P.IsHermitian) (hPP : P * P = P)
    (htr : P.trace = 2) (hPC : P * C = C) :
    formR C = frobSq (C - (C.trace / 2) • P) := by
  sorry

/-- Section 1 (`d = 3`): the partial trace over site 1 of a coefficient matrix of rank at most two
can have rank three. -/
theorem rank_raise_ptrace :
    ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ (ptrace₁ C).rank = 3 := by
  sorry

/-- PPT region (`d = 3`, `α ≤ 1/3`): the partial transpose of three copies of the Werner state
is positive semidefinite, so no vector of any Schmidt rank detects three copies. -/
theorem three_copy_ppt_of_le_third {α : ℝ} (h : α ≤ 1 / 3) :
    (partialTranspose (tripleCopy (werner 3 α))).PosSemidef := by
  sorry

/-- The `d = 2` remark on Theorem 2.1: the qubit Werner state at `α = 1/2` is separable (for `α ≤ 1`
it is NPT exactly when `α > 1/2`, `werner_npt_iff` at `d = 2`). -/
theorem werner_two_half_separable : IsBipartiteSeparable (werner 2 (1 / 2)) := by
  sorry

/-- Corollary 6.2: `noisyFamily J p` has full rank for `0 ≤ p < 1`. -/
theorem noisy_family_posDef {d : ℕ} (J : Matrix (Fin d) (Fin 3) ℂ) (hd : 0 < d) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1) : (noisyFamily J p).PosDef := by
  sorry

/-- Corollary 6.2: for an isometry `J : ℂ³ → ℂᵈ`, `noisyFamily J p` is NPT for
`15/(d² + 15) < p ≤ 1`. (Its three-copy nondistillability follows from T2.1a:
`noisy_family_three_copy_of_endpoint`.) -/
theorem noisy_family_npt {d : ℕ} (J : Matrix (Fin d) (Fin 3) ℂ) (hJ : J.conjTranspose * J = 1)
    (hd : 0 < d) {p : ℝ} (hp : 15 / ((d : ℝ) ^ 2 + 15) < p) (hp1 : p ≤ 1) :
    IsNPT (noisyFamily J p) := by
  sorry

/-- Implication from T2.1a: Theorem 2.1, eq. (4), as an attained minimum (`IsLeast`) over
normalized matrices of rank at most two. -/
theorem sharp_minimum_isLeast_of_endpoint : QutritEndpointInequality →
    ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 / 2 →
      IsLeast {x : ℝ | ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
        C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = x} (sharpCurve α) := by
  sorry

/-- Theorem 5.1, inclusion "⊇" (`d = 3`): every member of the union of families I–III (each family
at every site placement, times a unit phase; `IsQutritZeroFamilyMember`) is a
normalized endpoint zero of rank at most two with `(C†C)² = C†C/2`, i.e. its nonzero singular values
are `1/√2`. -/
theorem zero_families_are_half_singular_zeros
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hC : IsQutritZeroFamilyMember C) :
    C.rank ≤ 2 ∧ invN C = 1 ∧ endpointEnergy C = 0 ∧
      C.conjTranspose * C * (C.conjTranspose * C) = (1 / 2 : ℂ) • (C.conjTranspose * C) := by
  sorry

/-- Section 4.1, eqs. (12)–(15): an exact endpoint certificate implies T2.1a. The hypotheses are the
certificate data: a Hermitian `Ph` (the carrier projector `Π_h`; only Hermiticity is assumed)
fixing every feature `z_h = vec C ⊗ p ⊗ p` with `C = X B`, `p = bivecMat X` (Appendix B), and
positive semidefinite `Gh, Gm, Ga` with `Π_h (T ⊗ I) Π_h = G_h + Π_h Γ₃₄(G_m) Π_h + Π_h Γ₁₂₃₄(G_a) Π_h`
(eq. (14); its support conditions `G_s = Π_s G_s Π_s` are not assumed). -/
theorem qutrit_endpoint_of_certificate
    (Ph Gh Gm Ga : Matrix SixRegisters SixRegisters ℂ) (hPh : Ph.conjTranspose = Ph)
    (hcarrier : ∀ (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
      (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ),
      Ph.mulVec (featureH (X * B) (bivecMat X)) = featureH (X * B) (bivecMat X))
    (hgram : Ph * sixRegisterOperator * Ph =
      Gh + Ph * partialTranspose Gm * Ph + Ph * minorTranspose Ga * Ph)
    (hpsd : Gh.PosSemidef ∧ Gm.PosSemidef ∧ Ga.PosSemidef) :
    QutritEndpointInequality := by
  sorry

/-- Implication T2.1a ⇒ Corollary 6.2: with the qutrit seed, `noisyFamily J p` is three-copy
nondistillable for `15/(d² + 15) < p < 1` (any `d`, `J` an isometry). -/
theorem noisy_family_three_copy_of_endpoint : QutritEndpointInequality →
    ∀ (d : ℕ) (J : Matrix (Fin d) (Fin 3) ℂ), J.conjTranspose * J = 1 → ∀ p : ℝ,
      15 / ((d : ℝ) ^ 2 + 15) < p → p < 1 → ¬ IsThreeCopyFilterDistillable (noisyFamily J p) := by
  sorry

/-- Section 3.1, eq. (11) in two-factor form: for an orthonormal pair `u₁, u₂` on `L ⊗ R`,
`∑_{r,s} e(u_r, u_s) = 2 Q(u₁u₁† + u₂u₂†)` (`biDefect`, `cutForm`). Here `e(u, v)` is defined by its
expanded form `‖u‖²‖v‖² + |⟨v, u⟩|² - ‖P(u v†)‖²`; that it is a squared norm (Appendix A), and so
`e ≥ 0`, is not part of this statement. -/
theorem projector_cut_identity {L R : Type*} [Fintype L] [Fintype R] (u₁ u₂ : L × R → ℂ)
    (h1 : vecNormSq u₁ = 1) (h2 : vecNormSq u₂ = 1) (h12 : braket u₁ u₂ = 0) :
    biDefect u₁ u₁ + biDefect u₁ u₂ + biDefect u₂ u₁ + biDefect u₂ u₂ =
      2 * cutForm (ketBra u₁ u₁ + ketBra u₂ u₂) := by
  sorry

/-- Section 3.1, eq. (11), right-hand side: `2 Q(P) = 6 - ‖Tr_L P‖_F² - ‖Tr_R P‖_F²` for the
projector `P = u₁u₁† + u₂u₂†` onto an orthonormal pair. -/
theorem cutForm_two_plane_projector {L R : Type*} [Fintype L] [Fintype R] (u₁ u₂ : L × R → ℂ)
    (h1 : vecNormSq u₁ = 1) (h2 : vecNormSq u₂ = 1) (h12 : braket u₁ u₂ = 0) :
    2 * cutForm (ketBra u₁ u₁ + ketBra u₂ u₂) =
      6 - frobSq (ptraceL (ketBra u₁ u₁ + ketBra u₂ u₂)) -
        frobSq (ptraceR (ketBra u₁ u₁ + ketBra u₂ u₂)) := by
  sorry

/-- Section 3.1: an orthonormal pair of fully product tensors whose sum is a product across the
cuts `1|23` and `2|13` has `|e₁⟩⟨e₁| + |e₂⟩⟨e₂| = (P_E) ⊗ |u⟩⟨u| ⊗ |v⟩⟨v|` with the two-plane
factor at site 1, 2 or 3. -/
theorem two_plane_product {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (a₁ b₁ : a → ℂ) (a₂ b₂ : b → ℂ) (a₃ b₃ : c → ℂ) (e₁ e₂ : a × b × c → ℂ)
    (he₁ : ∀ i j k, e₁ (i, j, k) = a₁ i * a₂ j * a₃ k)
    (he₂ : ∀ i j k, e₂ (i, j, k) = b₁ i * b₂ j * b₃ k)
    (hn₁ : vecNormSq e₁ = 1) (hn₂ : vecNormSq e₂ = 1) (ho : braket e₁ e₂ = 0)
    (hcut₁ : ∃ (α : a → ℂ) (β : b × c → ℂ), ∀ i j k, e₁ (i, j, k) + e₂ (i, j, k) = α i * β (j, k))
    (hcut₂ : ∃ (α : b → ℂ) (β : a × c → ℂ), ∀ i j k, e₁ (i, j, k) + e₂ (i, j, k) = α j * β (i, k)) :
    (∃ (f₁ f₂ : a → ℂ) (u : b → ℂ) (v : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        ketBra e₁ e₁ + ketBra e₂ e₂ = tensor₃ (ketBra f₁ f₁ + ketBra f₂ f₂) (ketBra u u) (ketBra v v)) ∨
    (∃ (u : a → ℂ) (f₁ f₂ : b → ℂ) (v : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        ketBra e₁ e₁ + ketBra e₂ e₂ = tensor₃ (ketBra u u) (ketBra f₁ f₁ + ketBra f₂ f₂) (ketBra v v)) ∨
    (∃ (u : a → ℂ) (v : b → ℂ) (f₁ f₂ : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        ketBra e₁ e₁ + ketBra e₂ e₂ = tensor₃ (ketBra u u) (ketBra v v) (ketBra f₁ f₁ + ketBra f₂ f₂)) := by
  sorry

/-- Peres–Horodecki two-qubit criterion, quoted in the proof of Corollary 2.2: a two-qubit operator
is separable (a finite nonnegative combination of products of positive semidefinite operators,
the zero operator included) exactly when it and its partial transpose are positive semidefinite. -/
theorem twoQubit_separable_iff_ppt
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    IsBipartiteSeparable ρ ↔ ρ.PosSemidef ∧ (partialTranspose ρ).PosSemidef := by
  sorry

open scoped Matrix

/-- Appendix C, first analytic input: a rank-two qutrit matrix with `C² = κ C` satisfies
`q(C) ≥ (s₁ - s₂)²/6` (`s₁`, `s₂` its two nonzero singular values; the bound is symmetric in them),
and at a zero its range and corange are both thin at a common site. -/
theorem appendixC_input1 :
  ∀ (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) (κ : ℂ), C.rank = 2 → C * C = κ • C →
    (frobSq C - 2 * Real.sqrt ((frobSq C ^ 2 - frobSq (Cᴴ * C)) / 2)) / 6 ≤ endpointEnergy C ∧
      (endpointEnergy C = 0 →
        ((ptrace₂₃ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₂₃ (Cᴴ * C)).rank ≤ 2) ∨
          ((ptrace₁₃ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₁₃ (Cᴴ * C)).rank ≤ 2) ∨
            ((ptrace₁₂ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₁₂ (Cᴴ * C)).rank ≤ 2)) := by
  sorry

/-- Appendix C, second analytic input: a rank-two endpoint zero whose range contains a nonzero fully
product vector has local range dimension at most two at every site. -/
theorem appendixC_input2 :
  ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank = 2 → endpointEnergy C = 0 →
    (∃ x : (Fin 3 × Fin 3 × Fin 3) → ℂ, C *ᵥ x ≠ 0 ∧ (∃ (u v w : Fin 3 → ℂ), ∀ p : Fin 3 × Fin 3 × Fin 3,
        (C *ᵥ x) p = u p.1 * v p.2.1 * w p.2.2)) →
      (ptrace₂₃ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₁₃ (C * Cᴴ)).rank ≤ 2 ∧ (ptrace₁₂ (C * Cᴴ)).rank ≤ 2 := by
  sorry

/-- Appendix C, third analytic input: a normalized endpoint zero of rank at most two with a thin
local range lies in the union of families I–III. -/
theorem appendixC_input3 :
  ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C.rank ≤ 2 → invN C = 1 → endpointEnergy C = 0 →
    ((ptrace₂₃ (C * Cᴴ)).rank ≤ 2 ∨ (ptrace₁₃ (C * Cᴴ)).rank ≤ 2 ∨ (ptrace₁₂ (C * Cᴴ)).rank ≤ 2) → IsQutritZeroFamilyMember C := by
  sorry

end ThreeCopyQutritWerner.Endpoints
