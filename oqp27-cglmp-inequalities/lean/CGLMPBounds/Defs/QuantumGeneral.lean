module

public import CGLMPBounds.Defs.Quantum

@[expose] public section


/-!
# Finite-dimensional quantum behaviours with POVMs (definitions)

Supplement, Theorem A.4: "The same supremum holds over arbitrary finite-dimensional quantum states and
finite-outcome POVMs"; Theorem F.3: "For arbitrary finite-dimensional states and POVMs"; Letter: "For
these rank-one measurements, probability white noise is exactly the behaviour of the maximally mixed
bipartite state ... the same isotropic state `v|Φ_d⟩⟨Φ_d| + (1 - v) I/d²`."

A state on `ℂ^{dA} ⊗ ℂ^{dB}` is a density matrix `ρ` indexed by `Fin dA × Fin dB` (the basis vector
`|i⟩ ⊗ |j⟩` has index `(i, j)`); a measurement is a POVM; the behaviour is
`q(a,b|x,y) = Tr(ρ (E_x(a) ⊗ F_y(b)))`, with the Kronecker product `⊗ₖ` of matrices.

* `IsPOVM E` : positive semidefinite elements summing to the identity;
* `IsDensityMatrix ρ` : positive semidefinite with unit trace;
* `quantumTable ρ E F` : the behaviour;
* `quantumBehaviours α β` : all behaviours of finite-dimensional states and POVMs with outcomes
  `α` (Alice) and `β` (Bob);
* `phiVec d`, `phiState d` : `|Φ_d⟩ = d^{-1/2} Σ_j |jj⟩` and `|Φ_d⟩⟨Φ_d|`.

This file contains definitions only (no theorems); it belongs to the statement dependency closure.
-/

open scoped ComplexOrder Kronecker

namespace CGLMPBounds

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

end CGLMPBounds
