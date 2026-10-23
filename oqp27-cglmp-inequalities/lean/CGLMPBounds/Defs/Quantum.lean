module

public import CGLMPBounds.Defs.Scenario

@[expose] public section


/-!
# Projective measurements on the maximally entangled state (definitions)

Letter, "The conjecture and its measurement theorem", and supplement Appendix B: "Fix the state
`|Φ_n⟩ = n^{-1/2} Σ_j |jj⟩`. A projective measurement is a set of orthogonal projections summing to
the identity; zero projections and unequal ranks are allowed. Writing the four measurements as
`(P⁰, P¹, P², P³) = (A₀ᵀ, B₀, A₁ᵀ, B₁)` gives `q(a,b|x,y) = n⁻¹ Tr(P^{2x}_a P^{1+2y}_b)`."

This file contains definitions only. `tracialTable` is the manuscript's tracial form of the physical
model; the model with the state vector and tensor products is `quantumTable` in
`Defs/QuantumGeneral.lean`, and `Quantum/Bridge.lean` proves that the two agree.
-/

namespace CGLMPBounds

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

end CGLMPBounds
