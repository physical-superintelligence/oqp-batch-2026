module

public import CausalNonpurifiability.Definitions.HeisenbergCore
public import CausalNonpurifiability.Definitions.Channels
public import CausalNonpurifiability.Purification.Unitary
public import CausalNonpurifiability.Purification.Sector

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

/-- `Φ†` is unital. -/
theorem heis_one (U : Matrix (F × K) N ℂ) (hU : Uᴴ * U = 1) : heis U 1 = 1 := by
  rw [heis, Matrix.one_kronecker_one, Matrix.mul_one, hU]

/-- `Φ†` is multiplicative; this uses `𝒰 𝒰† = 1`, that is, the purity of `S`. -/
theorem heis_mul (U : Matrix (F × K) N ℂ) (hU : U * Uᴴ = 1) (Q₁ Q₂ : Matrix K K ℂ) :
    heis U (Q₁ * Q₂) = heis U Q₁ * heis U Q₂ := by
  have hk : ((1 : Matrix F F ℂ) ⊗ₖ (Q₁ * Q₂)) =
      ((1 : Matrix F F ℂ) ⊗ₖ Q₁) * ((1 : Matrix F F ℂ) ⊗ₖ Q₂) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have h1 : Uᴴ * (((1 : Matrix F F ℂ) ⊗ₖ Q₁) * ((1 : Matrix F F ℂ) ⊗ₖ Q₂)) * U =
      Uᴴ * ((1 : Matrix F F ℂ) ⊗ₖ Q₁) * (1 : Matrix (F × K) (F × K) ℂ) *
        (((1 : Matrix F F ℂ) ⊗ₖ Q₂) * U) := by
    rw [Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  unfold heis
  rw [hk, h1, ← hU]
  simp only [Matrix.mul_assoc]

/-- `Φ†` preserves adjoints. -/
theorem heis_conjTranspose (U : Matrix (F × K) N ℂ) (Q : Matrix K K ℂ) :
    (heis U Q)ᴴ = heis U Qᴴ := by
  unfold heis
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Matrix.mul_assoc]

/-- Entries of `𝒰†(I_F ⊗ Q)`: the sum over the future index collapses. -/
theorem conjTranspose_mul_one_kronecker_apply (U : Matrix (F × K) N ℂ) (Q : Matrix K K ℂ)
    (a : N) (z : F) (k : K) :
    (Uᴴ * ((1 : Matrix F F ℂ) ⊗ₖ Q)) a (z, k) = ∑ k', star (U (z, k') a) * Q k' k := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single z]
  · refine Finset.sum_congr rfl fun k' _ => ?_
    simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
      one_mul]
  · intro z' _ hz'
    refine Finset.sum_eq_zero fun k' _ => ?_
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_ne hz', zero_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Entry formula for `Φ†(Q)`. -/
theorem heis_apply (U : Matrix (F × K) N ℂ) (Q : Matrix K K ℂ) (a b : N) :
    heis U Q a b = ∑ z, ∑ k, (∑ k', star (U (z, k') a) * Q k' k) * U (z, k) b := by
  rw [heis, Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun k _ => ?_
  rw [conjTranspose_mul_one_kronecker_apply]

end Heisenberg

end CausalNonpurifiability
