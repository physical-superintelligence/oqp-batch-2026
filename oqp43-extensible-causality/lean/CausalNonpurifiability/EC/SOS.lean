module

public import Mathlib
public import CausalNonpurifiability.Linear.Positive

@[expose] public section


/-!
# `CausalNonpurifiability.EC.SOS`

Dimension-free noncommutative sum of squares.

* `dXor E H := E + H - 2 * E * H` — the operator `D_{ij} = E_i + H_j - 2 E_i H_j` of
  `eq:operator-SOS` / `eq:DC`.
* `operator_sos_two` — the denominator-cleared ring identity
  `2 (37 D₀₀ + 7 D₀₁ + 7 D₁₀ − 3 D₁₁) = 32 (E₀−H₀)² + L² + 7 M² + 88 (E₀−E₀²+H₀−H₀²) + 8 (E₁−E₁²+H₁−H₁²)`
  with `L = 7E₀ + E₁ − 7H₀ − H₁`, `M = −E₀ + E₁ − H₀ + H₁`, in an arbitrary ring with
  exactly the four cross-party commutation premises `[E_i, H_j] = 0` (no same-side
  commutation).  It is `eq:operator-SOS` multiplied by `2`, i.e. the
  operator expansion of the Gram identity `eq:Gram`.
* `sos_psd_of_commute` — for four effects with cross commutation, the operator
  `37 D₀₀ + 7 D₀₁ + 7 D₁₀ − 3 D₁₁` is PSD (`eq:operator-SOS`, `≥ 0`).
* `sos_matrix_psd` — the same on `RA × RB` for `E_i ⊗ₖ 1`, `1 ⊗ₖ H_j`, with cross
  commutation from `Matrix.mul_kronecker_mul`.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

/-- `D(E, H) = E + H - 2 E H`: the operator symmetric difference of two effects, the
`D_{ij} = E_i + H_j - 2 E_i H_j` of `eq:operator-SOS` and the integrand of `eq:DC`. -/
def dXor {R : Type*} [Ring R] (E H : R) : R :=
  E + H - 2 * E * H

/-- Square of a difference of commuting elements: `(a - b)² = a² - 2ab + b²`. -/
theorem sq_sub_of_commute {R : Type*} [Ring R] {a b : R} (h : Commute a b) :
    (a - b) ^ 2 = a ^ 2 - 2 * (a * b) + b ^ 2 := by
  calc (a - b) ^ 2 = a * a - a * b - b * a + b * b := by noncomm_ring
    _ = a * a - a * b - a * b + b * b := by rw [h.eq]
    _ = a ^ 2 - 2 * (a * b) + b ^ 2 := by noncomm_ring

/-- **Denominator-cleared operator SOS** (`eq:operator-SOS` times two).
Valid in any ring given only the four cross-party commutations `[E_i, H_j] = 0`;
nothing is assumed about `E₀E₁` or `H₀H₁`. -/
theorem operator_sos_two {R : Type*} [Ring R] (E0 E1 H0 H1 : R)
    (h00 : Commute E0 H0) (h01 : Commute E0 H1)
    (h10 : Commute E1 H0) (h11 : Commute E1 H1) :
    2 * (37 * dXor E0 H0 + 7 * dXor E0 H1 + 7 * dXor E1 H0 - 3 * dXor E1 H1) =
      32 * (E0 - H0) ^ 2 + (7 * E0 + E1 - 7 * H0 - H1) ^ 2
        + 7 * (-E0 + E1 - H0 + H1) ^ 2
        + 88 * (E0 - E0 ^ 2 + H0 - H0 ^ 2) + 8 * (E1 - E1 ^ 2 + H1 - H1 ^ 2) := by
  -- Alice-side combinations commute with Bob-side combinations.
  have c7 : Commute (7 * E0 + E1) (7 * H0 + H1) := by
    show (7 * E0 + E1) * (7 * H0 + H1) = (7 * H0 + H1) * (7 * E0 + E1)
    calc (7 * E0 + E1) * (7 * H0 + H1)
        = 49 * (E0 * H0) + 7 * (E0 * H1) + 7 * (E1 * H0) + E1 * H1 := by noncomm_ring
      _ = 49 * (H0 * E0) + 7 * (H1 * E0) + 7 * (H0 * E1) + H1 * E1 := by
          rw [h00.eq, h01.eq, h10.eq, h11.eq]
      _ = (7 * H0 + H1) * (7 * E0 + E1) := by noncomm_ring
  have cm : Commute (-E0 + E1) (H0 - H1) :=
    (h00.neg_left.add_left h10).sub_right (h01.neg_left.add_left h11)
  -- Expand the three cross squares with the commutation folded in.
  have s1 : (E0 - H0) ^ 2 = E0 ^ 2 - 2 * (E0 * H0) + H0 ^ 2 := sq_sub_of_commute h00
  have s2 : (7 * E0 + E1 - 7 * H0 - H1) ^ 2
      = (7 * E0 + E1) ^ 2 - 2 * ((7 * E0 + E1) * (7 * H0 + H1)) + (7 * H0 + H1) ^ 2 := by
    rw [sub_sub]; exact sq_sub_of_commute c7
  have s3 : (-E0 + E1 - H0 + H1) ^ 2
      = (-E0 + E1) ^ 2 - 2 * ((-E0 + E1) * (H0 - H1)) + (H0 - H1) ^ 2 := by
    rw [sub_add]; exact sq_sub_of_commute cm
  rw [s1, s2, s3]
  simp only [dXor]
  noncomm_ring

section Matrices

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Operator SOS positivity** (`eq:operator-SOS`, `≥ 0`): for effects `X₀ X₁ Y₀ Y₁` on a
common space with `[X_i, Y_j] = 0`, the operator `37 D₀₀ + 7 D₀₁ + 7 D₁₀ − 3 D₁₁` is PSD.
Every summand of `operator_sos_two`'s right-hand side is a Hermitian square or
`88 (F − F²)`, `8 (F − F²)` for effects `F`; the factor two is removed at the end. -/
theorem sos_psd_of_commute {X0 X1 Y0 Y1 : Matrix ι ι ℂ}
    (hX0 : Effect X0) (hX1 : Effect X1) (hY0 : Effect Y0) (hY1 : Effect Y1)
    (h00 : Commute X0 Y0) (h01 : Commute X0 Y1) (h10 : Commute X1 Y0) (h11 : Commute X1 Y1) :
    ((37 : ℕ) • dXor X0 Y0 + (7 : ℕ) • dXor X0 Y1 + (7 : ℕ) • dXor X1 Y0
      - (3 : ℕ) • dXor X1 Y1).PosSemidef := by
  have key := operator_sos_two X0 X1 Y0 Y1 h00 h01 h10 h11
  have e0 : X0.IsHermitian := hX0.isHermitian
  have e1 : X1.IsHermitian := hX1.isHermitian
  have f0 : Y0.IsHermitian := hY0.isHermitian
  have f1 : Y1.IsHermitian := hY1.isHermitian
  -- The right-hand side of the identity is PSD term by term.
  have hR : (32 * (X0 - Y0) ^ 2 + (7 * X0 + X1 - 7 * Y0 - Y1) ^ 2
      + 7 * (-X0 + X1 - Y0 + Y1) ^ 2
      + 88 * (X0 - X0 ^ 2 + Y0 - Y0 ^ 2) + 8 * (X1 - X1 ^ 2 + Y1 - Y1 ^ 2)).PosSemidef := by
    have t1 : (32 * (X0 - Y0) ^ 2).PosSemidef :=
      posSemidef_ofNat_mul (hermitian_sq_psd (e0.sub f0)) 32
    have t2 : ((7 * X0 + X1 - 7 * Y0 - Y1) ^ 2).PosSemidef :=
      hermitian_sq_psd
        ((((isHermitian_ofNat_mul e0 7).add e1).sub (isHermitian_ofNat_mul f0 7)).sub f1)
    have t3 : (7 * (-X0 + X1 - Y0 + Y1) ^ 2).PosSemidef :=
      posSemidef_ofNat_mul (hermitian_sq_psd (((e0.neg.add e1).sub f0).add f1)) 7
    have t4 : (88 * (X0 - X0 ^ 2 + Y0 - Y0 ^ 2)).PosSemidef := by
      refine posSemidef_ofNat_mul ?_ 88
      rw [add_sub_assoc]
      exact (effect_sub_sq_psd' hX0).add (effect_sub_sq_psd' hY0)
    have t5 : (8 * (X1 - X1 ^ 2 + Y1 - Y1 ^ 2)).PosSemidef := by
      refine posSemidef_ofNat_mul ?_ 8
      rw [add_sub_assoc]
      exact (effect_sub_sq_psd' hX1).add (effect_sub_sq_psd' hY1)
    exact (((t1.add t2).add t3).add t4).add t5
  have h2 : (2 * (37 * dXor X0 Y0 + 7 * dXor X0 Y1 + 7 * dXor X1 Y0
      - 3 * dXor X1 Y1)).PosSemidef := by
    rw [key]; exact hR
  have h3 := posSemidef_of_two_mul h2
  simpa only [nsmul_eq_mul, Nat.cast_ofNat] using h3

end Matrices

section Kronecker

variable {RA RB : Type} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]

/-- Cross-party commutation `[E ⊗ 1, 1 ⊗ H] = 0` on `RA × RB`, from
`(A * B) ⊗ₖ (A' * B') = (A ⊗ₖ A') * (B ⊗ₖ B')` (`Matrix.mul_kronecker_mul`); both products
equal `E ⊗ₖ H` ("extended by opposite-side identities, so `[E_i, H_j] = 0`",
`eq:operator-SOS`). -/
theorem commute_kronecker_one_one_kronecker (E : Matrix RA RA ℂ) (H : Matrix RB RB ℂ) :
    Commute (E ⊗ₖ (1 : Matrix RB RB ℂ)) ((1 : Matrix RA RA ℂ) ⊗ₖ H) := by
  show (E ⊗ₖ (1 : Matrix RB RB ℂ)) * ((1 : Matrix RA RA ℂ) ⊗ₖ H)
    = ((1 : Matrix RA RA ℂ) ⊗ₖ H) * (E ⊗ₖ (1 : Matrix RB RB ℂ))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]

/-- **`eq:operator-SOS` on `RA × RB`**: for effects `E₀ E₁` on `RA` and `H₀ H₁` on `RB`,
`37 D₀₀ + 7 D₀₁ + 7 D₁₀ − 3 D₁₁ ≥ 0` with `D_{ij} = dXor (E_i ⊗ₖ 1) (1 ⊗ₖ H_j)`.
This is the dimension-free certificate behind `eq:DC`: it holds for arbitrary finite
ancillary dimensions, singular and nonprojective effects. -/
theorem sos_matrix_psd {E0 E1 : Matrix RA RA ℂ} {H0 H1 : Matrix RB RB ℂ}
    (hE0 : Effect E0) (hE1 : Effect E1) (hH0 : Effect H0) (hH1 : Effect H1) :
    ((37 : ℕ) • dXor (E0 ⊗ₖ (1 : Matrix RB RB ℂ)) ((1 : Matrix RA RA ℂ) ⊗ₖ H0)
      + (7 : ℕ) • dXor (E0 ⊗ₖ (1 : Matrix RB RB ℂ)) ((1 : Matrix RA RA ℂ) ⊗ₖ H1)
      + (7 : ℕ) • dXor (E1 ⊗ₖ (1 : Matrix RB RB ℂ)) ((1 : Matrix RA RA ℂ) ⊗ₖ H0)
      - (3 : ℕ) • dXor (E1 ⊗ₖ (1 : Matrix RB RB ℂ)) ((1 : Matrix RA RA ℂ) ⊗ₖ H1)).PosSemidef :=
  sos_psd_of_commute (effect_kronecker_one hE0) (effect_kronecker_one hE1)
    (effect_one_kronecker hH0) (effect_one_kronecker hH1)
    (commute_kronecker_one_one_kronecker E0 H0) (commute_kronecker_one_one_kronecker E0 H1)
    (commute_kronecker_one_one_kronecker E1 H0) (commute_kronecker_one_one_kronecker E1 H1)

end Kronecker

end CausalNonpurifiability
