module

public import CGLMPBounds

@[expose] public section

/-!
# Proofs of the statements of `Challenge.lean`

The definitions below are the definition block of `Challenge.lean`, unchanged and in the same order
(Comparator checks that they are the same constants). `OQP27.Bridge` proves that each of them agrees
with its counterpart in the library `CGLMPBounds` (by `rfl`, and by `Iff` for the five structures).
Each theorem then has the same name and statement as in `Challenge.lean` (the statement text is copied
from there) and is proved from the library.
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

/-! ## The copied definitions agree with the library's -/

namespace OQP27.Bridge

universe u v

theorem table_eq : OQP27.Table.{u, v} = CGLMPBounds.Table.{u, v} := rfl
theorem strategy_eq : OQP27.Strategy.{u, v} = CGLMPBounds.Strategy.{u, v} := rfl
theorem detTable_eq : @OQP27.detTable.{u, v} = @CGLMPBounds.detTable.{u, v} := rfl
theorem localSet_eq : @OQP27.localSet.{u, v} = @CGLMPBounds.localSet.{u, v} := rfl
theorem uniformTable_eq : @OQP27.uniformTable.{u, v} = @CGLMPBounds.uniformTable.{u, v} := rfl
theorem noisy_eq : @OQP27.noisy.{u, v} = @CGLMPBounds.noisy.{u, v} := rfl
theorem residual_eq : OQP27.residual = CGLMPBounds.residual := rfl
theorem cglmpS_eq : @OQP27.cglmpS = @CGLMPBounds.cglmpS := rfl
theorem cglmp_eq : @OQP27.cglmp = @CGLMPBounds.cglmp := rfl
theorem cglmpFourierValue_eq : OQP27.cglmpFourierValue = CGLMPBounds.cglmpFourierValue := rfl
theorem tracialTable_eq : @OQP27.tracialTable.{u, v} = @CGLMPBounds.tracialTable.{u, v} := rfl
theorem fourierVector_eq : OQP27.fourierVector = CGLMPBounds.fourierVector := rfl
theorem fourierProjector_eq : OQP27.fourierProjector = CGLMPBounds.fourierProjector := rfl
theorem fourierTable_eq : OQP27.fourierTable = CGLMPBounds.fourierTable := rfl
theorem critVisibility_eq : @OQP27.critVisibility.{u, v} = @CGLMPBounds.critVisibility.{u, v} := rfl
theorem relEntropy_eq : @OQP27.relEntropy.{u} = @CGLMPBounds.relEntropy.{u} := rfl
theorem statStrength_eq : @OQP27.statStrength.{u, v} = @CGLMPBounds.statStrength.{u, v} := rfl
theorem pauliZ_eq : OQP27.TensorCHSH.pauliZ = CGLMPBounds.TensorCHSH.pauliZ := rfl
theorem pauliX_eq : OQP27.TensorCHSH.pauliX = CGLMPBounds.TensorCHSH.pauliX := rfl
theorem chshObservable_eq : OQP27.TensorCHSH.chshObservable = CGLMPBounds.TensorCHSH.chshObservable :=
  rfl
theorem qubitProjector_eq : OQP27.TensorCHSH.qubitProjector = CGLMPBounds.TensorCHSH.qubitProjector :=
  rfl
theorem tensorProjector_eq :
    OQP27.TensorCHSH.tensorProjector = CGLMPBounds.TensorCHSH.tensorProjector := rfl
theorem tensorProjectorFin_eq :
    OQP27.TensorCHSH.tensorProjectorFin = CGLMPBounds.TensorCHSH.tensorProjectorFin := rfl
theorem tensorCHSHTable_eq :
    OQP27.TensorCHSH.tensorCHSHTable = CGLMPBounds.TensorCHSH.tensorCHSHTable := rfl
theorem quantumTable_eq : @OQP27.quantumTable.{u, v} = @CGLMPBounds.quantumTable.{u, v} := rfl
theorem phiVec_eq : OQP27.phiVec = CGLMPBounds.phiVec := rfl
theorem phiState_eq : OQP27.phiState = CGLMPBounds.phiState := rfl
theorem bgpL_eq : OQP27.bgpL = CGLMPBounds.bgpL := rfl
theorem bgpH_eq : OQP27.bgpH = CGLMPBounds.bgpH := rfl
theorem bgpIndex_eq : OQP27.bgpIndex = CGLMPBounds.bgpIndex := rfl
theorem bgpFunctional_eq : OQP27.bgpFunctional = CGLMPBounds.bgpFunctional := rfl

theorem isBehaviour_iff {α : Type u} {β : Type v} [Fintype α] [Fintype β] (q : OQP27.Table α β) :
    OQP27.IsBehaviour q ↔ CGLMPBounds.IsBehaviour q :=
  ⟨fun h => ⟨h.nonneg, h.sum_eq_one⟩, fun h => ⟨h.nonneg, h.sum_eq_one⟩⟩

theorem isNoSignalling_iff {α : Type u} {β : Type v} [Fintype α] [Fintype β] (q : OQP27.Table α β) :
    OQP27.IsNoSignalling q ↔ CGLMPBounds.IsNoSignalling q :=
  ⟨fun h => ⟨(isBehaviour_iff q).1 h.isBehaviour, h.margA_indep, h.margB_indep⟩,
    fun h => ⟨(isBehaviour_iff q).2 h.isBehaviour, h.margA_indep, h.margB_indep⟩⟩

theorem isPVM_iff {n : ℕ} {α : Type u} [Fintype α] (P : α → Matrix (Fin n) (Fin n) ℂ) :
    OQP27.IsPVM P ↔ CGLMPBounds.IsPVM P :=
  ⟨fun h => ⟨h.isHermitian, h.mul_self, h.sum_eq_one⟩,
    fun h => ⟨h.isHermitian, h.mul_self, h.sum_eq_one⟩⟩

theorem isPOVM_iff {m : ℕ} {α : Type u} [Fintype α] (E : α → Matrix (Fin m) (Fin m) ℂ) :
    OQP27.IsPOVM E ↔ CGLMPBounds.IsPOVM E :=
  ⟨fun h => ⟨h.posSemidef, h.sum_eq_one⟩, fun h => ⟨h.posSemidef, h.sum_eq_one⟩⟩

theorem isDensityMatrix_iff {ι : Type u} [Fintype ι] (ρ : Matrix ι ι ℂ) :
    OQP27.IsDensityMatrix ρ ↔ CGLMPBounds.IsDensityMatrix ρ :=
  ⟨fun h => ⟨h.posSemidef, h.trace_eq_one⟩, fun h => ⟨h.posSemidef, h.trace_eq_one⟩⟩

theorem setOf_isNoSignalling_eq (α : Type u) (β : Type v) [Fintype α] [Fintype β] :
    {q : OQP27.Table α β | OQP27.IsNoSignalling q} =
      {q : CGLMPBounds.Table α β | CGLMPBounds.IsNoSignalling q} :=
  Set.ext fun q => isNoSignalling_iff q

theorem quantumBehaviours_eq (α : Type u) (β : Type v) [Fintype α] [Fintype β] :
    OQP27.quantumBehaviours α β = CGLMPBounds.quantumBehaviours α β := by
  ext q
  constructor
  · rintro ⟨dA, dB, ρ, E, F, hρ, hE, hF, rfl⟩
    exact ⟨dA, dB, ρ, E, F, (isDensityMatrix_iff ρ).1 hρ, fun x => (isPOVM_iff (E x)).1 (hE x),
      fun y => (isPOVM_iff (F y)).1 (hF y), rfl⟩
  · rintro ⟨dA, dB, ρ, E, F, hρ, hE, hF, rfl⟩
    exact ⟨dA, dB, ρ, E, F, (isDensityMatrix_iff ρ).2 hρ, fun x => (isPOVM_iff (E x)).2 (hE x),
      fun y => (isPOVM_iff (F y)).2 (hF y), rfl⟩

end OQP27.Bridge

section Statements

open scoped Matrix Kronecker

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
  have hP' : ∀ t, CGLMPBounds.IsPVM (P t) := fun t => (OQP27.Bridge.isPVM_iff (P t)).1 (hP t)
  exact ⟨CGLMPBounds.cglmp_projective_bound hd P hP', CGLMPBounds.cglmp_eq_fourier_iff_standard hd P hP'⟩

theorem OQP27.partB_noise_resistance_not_optimal (m : ℕ) (hm : 955 ≤ m) :
    OQP27.critVisibility (OQP27.TensorCHSH.tensorCHSHTable m)
      < OQP27.critVisibility (OQP27.fourierTable (2 ^ m)) := by
  have h := CGLMPBounds.noise_separation_955 m hm
  exact h.1.trans h.2

theorem OQP27.partB_kl_discrimination_not_optimal (m : ℕ) (hm : 41 ≤ m) :
    (⨆ μ ∈ {μ : Fin 2 → Fin 2 → ℝ | (∀ x y, 0 ≤ μ x y) ∧ ∑ x, ∑ y, μ x y = 1},
        OQP27.statStrength μ (OQP27.fourierTable (2 ^ m)))
      < OQP27.statStrength (fun _ _ => 1 / 4) (OQP27.TensorCHSH.tensorCHSHTable m) := by
  have h := CGLMPBounds.statistical_separation_spec m hm
  exact (h.2.2.trans_le (ENNReal.ofReal_le_ofReal h.2.1.le)).trans h.1

theorem OQP27.cglmp_local_bound (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ q ∈ OQP27.localSet (ZMod d) (ZMod d), OQP27.cglmp d q ≤ 2) ∧
      ∃ q ∈ OQP27.localSet (ZMod d) (ZMod d), OQP27.cglmp d q = 2 := by
  exact ⟨fun q hq => CGLMPBounds.cglmp_le_two d hd hq, CGLMPBounds.exists_mem_localSet_cglmp_eq_two d hd⟩

theorem OQP27.fourier_attains_cglmp_value (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    OQP27.cglmp d (OQP27.fourierTable d) = OQP27.cglmpFourierValue d ∧
      2 < OQP27.cglmpFourierValue d ∧
      ∀ v : ℝ, 2 < OQP27.cglmp d (OQP27.noisy v (OQP27.fourierTable d))
        ↔ 2 / OQP27.cglmpFourierValue d < v := by
  exact CGLMPBounds.fourier_attains_cglmp_value_spec d hd

theorem OQP27.fourier_projectors_pvm (d : ℕ) [NeZero d] (t : ℕ) :
    OQP27.IsPVM (OQP27.fourierProjector d t) := by
  exact (OQP27.Bridge.isPVM_iff _).2 (CGLMPBounds.fourierProjector_isPVM d t)

theorem OQP27.tracial_table_physical (n : ℕ) [NeZero n] {α β : Type*} [Fintype α] [Fintype β]
    (A : Fin 2 → α → Matrix (Fin n) (Fin n) ℂ) (B : Fin 2 → β → Matrix (Fin n) (Fin n) ℂ) :
    OQP27.IsDensityMatrix (OQP27.phiState n) ∧
      OQP27.quantumTable (OQP27.phiState n) (fun x a => Matrix.transpose (A x a)) B
        = OQP27.tracialTable A B ∧
      ((∀ x, OQP27.IsPVM (A x)) → (∀ y, OQP27.IsPVM (B y)) →
        (∀ x, OQP27.IsPVM (fun a => Matrix.transpose (A x a))) ∧
          OQP27.tracialTable A B ∈ OQP27.quantumBehaviours α β) := by
  obtain ⟨h1, h2, h3⟩ := CGLMPBounds.tracial_table_physical_spec A B
  refine ⟨(OQP27.Bridge.isDensityMatrix_iff _).2 h1, h2, fun hA hB => ?_⟩
  obtain ⟨h4, h5⟩ := h3 (fun x => (OQP27.Bridge.isPVM_iff _).1 (hA x))
    (fun y => (OQP27.Bridge.isPVM_iff _).1 (hB y))
  refine ⟨fun x => (OQP27.Bridge.isPVM_iff _).2 (h4 x), ?_⟩
  rw [OQP27.Bridge.quantumBehaviours_eq]
  exact h5

theorem OQP27.tensor_chsh_rank_one_pvm (m : ℕ) (t : Fin 4) :
    OQP27.IsPVM (OQP27.TensorCHSH.tensorProjectorFin m t.val) ∧
      (∀ a : Fin m → Bool,
        Matrix.trace (OQP27.TensorCHSH.tensorProjectorFin m t.val a) = (1 : ℂ)) ∧
      ∀ a : Fin m → Bool,
        (OQP27.TensorCHSH.tensorProjectorFin m t.val a).rank = 1 := by
  obtain ⟨h1, h2, h3⟩ := CGLMPBounds.TensorCHSH.tensorProjectorFin_rankOnePVM_spec m t
  exact ⟨(OQP27.Bridge.isPVM_iff _).2 h1, h2, h3⟩

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
  exact CGLMPBounds.cglmp_witness_tolerance hd P (fun t => (OQP27.Bridge.isPVM_iff (P t)).1 (hP t))
    hviolation

theorem OQP27.noise_separation_955 (m : ℕ) (hm : 955 ≤ m) :
    OQP27.critVisibility (OQP27.TensorCHSH.tensorCHSHTable m) < 3049 / 5000 ∧
      (3049 : ℝ) / 5000 < OQP27.critVisibility (OQP27.fourierTable (2 ^ m)) := by
  exact CGLMPBounds.noise_separation_955 m hm

theorem OQP27.statistical_separation (m : ℕ) (hm : 41 ≤ m) :
    ENNReal.ofReal (9 / 14 * Real.logb 2 (4 / 3))
        < OQP27.statStrength (fun _ _ => 1 / 4) (OQP27.TensorCHSH.tensorCHSHTable m) ∧
      (16 / 25 : ℝ) * Real.logb 2 (4 / 3) < 9 / 14 * Real.logb 2 (4 / 3) ∧
      (⨆ μ ∈ {μ : Fin 2 → Fin 2 → ℝ | (∀ x y, 0 ≤ μ x y) ∧ ∑ x, ∑ y, μ x y = 1},
          OQP27.statStrength μ (OQP27.fourierTable (2 ^ m)))
        < ENNReal.ofReal (16 / 25 * Real.logb 2 (4 / 3)) := by
  exact CGLMPBounds.statistical_separation_spec m hm

theorem OQP27.bgp_facet :
    Module.finrank ℝ (vectorSpan ℝ (OQP27.localSet (Fin 4) (Fin 4))) = 48 ∧
      Module.finrank ℝ (vectorSpan ℝ (OQP27.localSet (Fin 4) (Fin 4) ∩
        {q | OQP27.bgpFunctional q = 0})) = 47 ∧
      ∀ q ∈ OQP27.localSet (Fin 4) (Fin 4), OQP27.bgpFunctional q ≤ 0 := by
  exact CGLMPBounds.bgp_facet_spec

theorem OQP27.bgp_relative_interior_point (pbar : OQP27.Table (Fin 4) (Fin 4))
    (hpbar : pbar = (1 / 72 : ℝ) • ∑ s ∈ Finset.univ.filter
      (fun s : OQP27.Strategy (Fin 4) (Fin 4) =>
        OQP27.bgpFunctional (OQP27.detTable s) = 0), OQP27.detTable s) :
    pbar ∈ OQP27.localSet (Fin 4) (Fin 4) ∧ OQP27.bgpFunctional pbar = 0 ∧
      OQP27.IsNoSignalling pbar ∧ (∀ x y a b, 1 / 72 ≤ pbar x y a b) ∧
      (∃ x y a b, pbar x y a b = 1 / 72) ∧
      pbar ∈ intrinsicInterior ℝ
        {q : OQP27.Table (Fin 4) (Fin 4) | OQP27.IsNoSignalling q} := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := CGLMPBounds.bgp_relative_interior_point_spec pbar hpbar
  refine ⟨h1, h2, (OQP27.Bridge.isNoSignalling_iff pbar).2 h3, h4, h5, ?_⟩
  rw [OQP27.Bridge.setOf_isNoSignalling_eq]
  exact h6

theorem OQP27.bgp_no_signalling_violation :
    ∃ p : OQP27.Table (Fin 4) (Fin 4), OQP27.IsNoSignalling p ∧
      (∀ x y a b, ∃ r : ℚ, p x y a b = r) ∧ OQP27.bgpFunctional p = 1 / 144 := by
  obtain ⟨p, h1, h2, h3⟩ := CGLMPBounds.bgp_no_signalling_violation_spec
  exact ⟨p, (OQP27.Bridge.isNoSignalling_iff p).2 h1, h2, h3⟩

theorem OQP27.bgp_not_cglmp_four :
    ¬ ∃ e : OQP27.Strategy (Fin 4) (Fin 4) ≃
        OQP27.Strategy (ZMod 4) (ZMod 4),
      ∀ s, OQP27.bgpFunctional (OQP27.detTable s) = 0 ↔
        OQP27.cglmp 4 (OQP27.detTable (e s)) = 2 := by
  exact CGLMPBounds.bgp_not_cglmp_four_spec

theorem OQP27.bgp_no_fusion {α β : Type*}
    (fA : Fin 2 → Fin 4 → α) (fB : Fin 2 → Fin 4 → β)
    (hf : (∃ x, ¬ Function.Injective (fA x)) ∨ (∃ y, ¬ Function.Injective (fB y))) :
    ¬ ∃ G : OQP27.Strategy α β → ℝ,
      ∀ s : OQP27.Strategy (Fin 4) (Fin 4),
        OQP27.bgpFunctional (OQP27.detTable s) =
          G (fun x => fA x (s.1 x), fun y => fB y (s.2 y)) := by
  exact CGLMPBounds.bgp_no_fusion_spec fA fB hf

end Statements
