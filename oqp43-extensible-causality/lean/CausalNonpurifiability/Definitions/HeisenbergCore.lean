module

public import CausalNonpurifiability.Linear.Indices

@[expose] public section


/-!
# `CausalNonpurifiability.Purification.Heisenberg`

Step 2 of the proof of Theorem 6.1 (manuscript Appendix A, `eq:Phi`): the map
`Φ†(Q) = 𝒰†(Q ⊗ I_F)𝒰` for the unitary `𝒰` of `Pure.exists_unitary`.

The matrix `U : Matrix (F × K) N ℂ` has its rows indexed by the global future `F` and the inputs
`K = A_I × B_I`, and its columns by `N = P × (A_O × B_O)`. This file contains the algebraic part:
`heis U` is unital (`Uᴴ * U = 1`), multiplicative (`U * Uᴴ = 1`; this is where purity is used),
preserves adjoints and is linear; `heis_apply` is its entry formula.

The family `W_τ`, the bridge between `W_τ` and `heis`, the consequences of `eq:LV` for `heis` and
the assembly of Theorem 6.1 are in `Purification/Family.lean`, `Sector.lean`, `Separation.lean`
and `Necessity.lean`.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

section Heisenberg

variable {F K N : Type} [Fintype F] [Fintype K] [Fintype N] [DecidableEq F] [DecidableEq K]
  [DecidableEq N]

/-- The Heisenberg-picture map `Φ†(Q) = 𝒰†(Q ⊗ I_F)𝒰` of `eq:Phi`. -/
def heis (U : Matrix (F × K) N ℂ) (Q : Matrix K K ℂ) : Matrix N N ℂ :=
  Uᴴ * ((1 : Matrix F F ℂ) ⊗ₖ Q) * U

theorem heis_add (U : Matrix (F × K) N ℂ) (Q₁ Q₂ : Matrix K K ℂ) :
    heis U (Q₁ + Q₂) = heis U Q₁ + heis U Q₂ := by
  unfold heis
  rw [Matrix.kronecker_add, Matrix.mul_add, Matrix.add_mul]

theorem heis_smul (U : Matrix (F × K) N ℂ) (c : ℂ) (Q : Matrix K K ℂ) :
    heis U (c • Q) = c • heis U Q := by
  unfold heis
  rw [Matrix.kronecker_smul, Matrix.mul_smul, Matrix.smul_mul]

end Heisenberg

end CausalNonpurifiability
