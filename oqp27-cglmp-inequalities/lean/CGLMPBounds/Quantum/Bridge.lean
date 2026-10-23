module

public import CGLMPBounds.Quantum.General

@[expose] public section


/-!
# The tracial form is the physical model on `Φ_n`

Supplement, Appendix B: "With `P⁰ = A₀ᵀ, P¹ = B₀, P² = A₁ᵀ, P³ = B₁`,
`q(a, b|x, y) = τ_n(P^{2x}_a P^{1+2y}_b)`." The tracial table `tracialTable A B` (with `A x` the
tracial `P^{2x}`, `B y` the tracial `P^{1+2y}`) is the behaviour of the state `|Φ_n⟩⟨Φ_n|` when
Alice's physical measurement elements are `(A x a)ᵀ` and Bob's are `B y b`. This holds for all
`n × n` matrices, and for PVMs the transposes again form PVMs. Every PVM-scope endpoint stated
for `tracialTable` is therefore a statement about projective measurements on `Φ_n` in the physical
model of `Defs/QuantumGeneral.lean`.

* `isPVM_transpose` : transposes of the elements of a PVM form a PVM;
* `tracial_table_physical_spec` : the form of the Challenge endpoint.
-/

open Matrix

namespace CGLMPBounds

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The transposes of the elements of a PVM form a PVM. -/
theorem isPVM_transpose {n : ℕ} {P : α → Matrix (Fin n) (Fin n) ℂ} (hP : IsPVM P) :
    IsPVM (fun a => (P a)ᵀ) where
  isHermitian a := (hP.isHermitian a).transpose
  mul_self a := by rw [← Matrix.transpose_mul, hP.mul_self a]
  sum_eq_one := by rw [← Matrix.transpose_sum, hP.sum_eq_one, Matrix.transpose_one]

/-- The tracial form on `Φ_n` in the form of the Challenge endpoint: `|Φ_n⟩⟨Φ_n|` is a density
matrix; `⟨Φ_n| Aᵀ ⊗ B |Φ_n⟩ = τ_n(A B)` entrywise for all matrices; for PVMs the physical
measurements `a ↦ (A x a)ᵀ` are PVMs and the tracial table is a finite-dimensional quantum
behaviour. -/
theorem tracial_table_physical_spec {n : ℕ} [NeZero n] (A : Fin 2 → α → Matrix (Fin n) (Fin n) ℂ)
    (B : Fin 2 → β → Matrix (Fin n) (Fin n) ℂ) :
    IsDensityMatrix (phiState n) ∧
      quantumTable (phiState n) (fun x a => (A x a)ᵀ) B = tracialTable A B ∧
      ((∀ x, IsPVM (A x)) → (∀ y, IsPVM (B y)) →
        (∀ x, IsPVM (fun a => (A x a)ᵀ)) ∧ tracialTable A B ∈ quantumBehaviours α β) :=
  ⟨phiState_isDensityMatrix n, quantumTable_phiState A B,
    fun hA hB => ⟨fun x => isPVM_transpose (hA x), tracialTable_mem_quantumBehaviours hA hB⟩⟩

end CGLMPBounds
