module

public import CGLMPBounds.Defs.Quantum

@[expose] public section


/-!
# The common-input tensor CHSH measurements (definitions)

Supplement, Appendix F.2: "Let `d = 2^m`, identify outcomes with bit strings, and use
`Φ_2^{⊗m} = Φ_{2^m}`. On each tensor factor measure `A₀ = Z`, `A₁ = X`, `B₀ = (Z + X)/√2`,
`B₁ = (Z − X)/√2`. Each party uses the same input on all factors and retains every bit. These are
two complete rank-one PVMs per party." (Letter: "the usual CHSH choices".)

Tracial convention as in `Defs/Quantum.lean`: `(P⁰, P¹, P², P³) = (A₀ᵀ, B₀, A₁ᵀ, B₁)`; the four
single-pair observables are real symmetric, so transposition is trivial. Outcome bit `c` labels the
eigenvalue `(-1)^c`. Strings are indexed by `Fin m → Fin 2` and identified with `Fin (2^m)` by
`finFunctionFinEquiv`. This file contains definitions only.
-/

namespace CGLMPBounds.TensorCHSH

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

end CGLMPBounds.TensorCHSH
