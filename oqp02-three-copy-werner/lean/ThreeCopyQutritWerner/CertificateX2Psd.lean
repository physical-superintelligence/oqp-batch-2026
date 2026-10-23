module

public import ThreeCopyQutritWerner.CertificateDiagonalDominance
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Positivity facts for the exact certificate (exact correction)

The certificate route proves T2.1a through `qutritEndpointInequality_of_block_residual`
(CertificateExactBlockBridge), whose positivity premises are `∀ b, (N b).PosSemidef` for the
finite block families `Nh`, `Nm`, `Na`. With an exact correction every block is checked exactly;
no trial-face margin and no perturbation bound is needed:

* untouched mixed/antiholomorphic blocks are Gram forms `c • A Aᴴ` with `c ≥ 0`
  (`certificateX2_gram_posSemidef`, `certificateX2_int_gram_posSemidef`, block families
  `certificateX2_blocks_posSemidef_of_gram_except`); no data check at all;
* a holomorphic block `N` (integer numerators) is face supported: `Pᵀ A P = d² N` for integer `P`
  (`certificateX2_int_posSemidef_of_face`), and its face block `A` is positive by an exact
  integer residual `t² A - C Cᵀ` that is symmetric and row dominant
  (`certificateX2_int_posSemidef_of_residual`);
* rational blocks `(1/den) • N` (`certificateX2_int_div_posSemidef`) and zero blocks.

Nothing here refers to the certificate data; the generated per-block modules supply the literal
checks (`decide +kernel`).
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

section X2Psd

variable {n k m : Type*} [Fintype n] [Fintype k] [Fintype m]

/-- A nonnegative real multiple, written with a complex scalar, preserves positivity. -/
theorem certificateX2_posSemidef_ofReal_smul {M : Matrix n n ℂ} (hM : M.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) : ((c : ℂ) • M).PosSemidef := by
  have e : (c : ℂ) • M = c • M := by
    ext i j
    first
    | (simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]; done)
    | rfl
    | (simp; done)
  rw [e]
  exact hM.smul hc

/-- A Gram form with a nonnegative real weight is positive semidefinite. -/
theorem certificateX2_gram_posSemidef (A : Matrix n k ℂ) {c : ℝ} (hc : 0 ≤ c) :
    ((c : ℂ) • (A * Aᴴ)).PosSemidef :=
  certificateX2_posSemidef_ofReal_smul (Matrix.posSemidef_self_mul_conjTranspose A) hc

/-- For an integer matrix the cast of the transpose is the conjugate transpose of the cast. -/
theorem certificateX2_int_map_transpose (A : Matrix n k ℤ) :
    Aᵀ.map (Int.castRingHom ℂ) = (A.map (Int.castRingHom ℂ))ᴴ := by
  ext i j
  first
  | (simp [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]; done)
  | (simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
      Int.coe_castRingHom, star_intCast]; done)

/-- The complex cast of an integer `A Aᵀ` is the Gram matrix of the cast. -/
theorem certificateX2_int_mul_transpose_map (A : Matrix n k ℤ) :
    (A * Aᵀ).map (Int.castRingHom ℂ) =
      A.map (Int.castRingHom ℂ) * (A.map (Int.castRingHom ℂ))ᴴ := by
  rw [Matrix.map_mul, certificateX2_int_map_transpose]

/-- Integer Gram forms are positive semidefinite after the complex cast. -/
theorem certificateX2_int_gram_posSemidef (A : Matrix n k ℤ) :
    ((A * Aᵀ).map (Int.castRingHom ℂ)).PosSemidef := by
  rw [certificateX2_int_mul_transpose_map]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Integer Gram forms with the face-margin scaling `(1/s)²` (as in the trial factors `Z/2^80`). -/
theorem certificateX2_int_gram_scaled_posSemidef (A : Matrix n k ℤ) (s : ℤ) :
    ((1 / (s : ℂ)) ^ 2 • (A * Aᵀ).map (Int.castRingHom ℂ)).PosSemidef := by
  have e : (1 / (s : ℂ)) ^ 2 = (((1 / (s : ℝ)) ^ 2 : ℝ) : ℂ) := by
    first
    | (push_cast; done)
    | (push_cast; ring)
    | (norm_cast; done)
    | (simp; done)
  rw [e]
  exact certificateX2_posSemidef_ofReal_smul (certificateX2_int_gram_posSemidef A) (by positivity)

/-- Rational blocks `(1/den) • N` with integer numerators and a positive denominator. -/
theorem certificateX2_int_div_posSemidef (N : Matrix n n ℤ) (den : ℤ) (hden : 0 < den)
    (hN : (N.map (Int.castRingHom ℂ)).PosSemidef) :
    ((1 / (den : ℂ)) • N.map (Int.castRingHom ℂ)).PosSemidef := by
  have e : (1 / (den : ℂ)) = ((1 / (den : ℝ) : ℝ) : ℂ) := by
    first
    | (push_cast; done)
    | (push_cast; ring)
    | (norm_cast; done)
    | (simp; done)
  have hpos : (0 : ℝ) ≤ 1 / (den : ℝ) := by
    have h0 : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
    exact div_nonneg zero_le_one h0.le
  rw [e]
  exact certificateX2_posSemidef_ofReal_smul hN hpos

/-- EXACT BLOCK POSITIVITY: if `R = t² A - CC` is a symmetric, row-dominant integer matrix and
`CC` is positive (for instance `CC = C Cᵀ`), then the integer matrix `A` is positive
semidefinite. `C` is any proposed approximate Cholesky factor; it has no correctness premise. -/
theorem certificateX2_int_posSemidef_of_residual [DecidableEq n] (A CC : Matrix n n ℤ) (t : ℤ)
    (ht : t ≠ 0) (hCC : (CC.map (Int.castRingHom ℂ)).PosSemidef)
    (hsym : (t ^ 2 • A - CC)ᵀ = t ^ 2 • A - CC)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, |(t ^ 2 • A - CC) i j| ≤ (t ^ 2 • A - CC) i i) :
    (A.map (Int.castRingHom ℂ)).PosSemidef := by
  have hR := certificate_integer_posSemidef_of_row_dominance (t ^ 2 • A - CC) hsym hrow
  have hsum := hR.add hCC
  have e1 : (t ^ 2 • A - CC).map (Int.castRingHom ℂ) + CC.map (Int.castRingHom ℂ) =
      (((t : ℝ) ^ 2 : ℝ) : ℂ) • A.map (Int.castRingHom ℂ) := by
    ext i j
    first
    | (simp only [Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul, Int.coe_castRingHom, Int.cast_sub, Int.cast_mul, Int.cast_pow,
        Complex.ofReal_pow, Complex.ofReal_intCast, sub_add_cancel]; done)
    | (simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply]; done)
    | (simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply]; ring)
  rw [e1] at hsum
  have hfin := certificateX2_posSemidef_ofReal_smul hsum
    (show (0 : ℝ) ≤ 1 / (t : ℝ) ^ 2 by positivity)
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have e2 : (((1 / (t : ℝ) ^ 2 : ℝ)) : ℂ) • ((((t : ℝ) ^ 2 : ℝ) : ℂ) •
      A.map (Int.castRingHom ℂ)) = A.map (Int.castRingHom ℂ) := by
    rw [smul_smul]
    have e3 : (((1 / (t : ℝ) ^ 2 : ℝ)) : ℂ) * (((t : ℝ) ^ 2 : ℝ) : ℂ) = 1 := by
      push_cast
      first
      | exact one_div_mul_cancel (pow_ne_zero 2 ht')
      | exact inv_mul_cancel₀ (pow_ne_zero 2 ht')
      | (field_simp; done)
    rw [e3, one_smul]
  rw [e2] at hfin
  exact hfin

/-- FACE-SUPPORTED BLOCKS: if `Pᵀ A P = d² N` with `d ≠ 0` and `A ⪰ 0`, then `N ⪰ 0`.
For a holomorphic block in the certificate's quadratic-form coordinates, `A = Kᵀ N K` is the face block and
`P` the first `dim K` rows of `d • [K L]⁻¹` (`L` the metric complement); the identity holds
exactly when the 2,463 quotient coordinates of the block vanish. -/
theorem certificateX2_int_posSemidef_of_face (N : Matrix m m ℤ) (A : Matrix n n ℤ)
    (P : Matrix n m ℤ) (d : ℤ) (hd : d ≠ 0) (hface : Pᵀ * A * P = d ^ 2 • N)
    (hA : (A.map (Int.castRingHom ℂ)).PosSemidef) : (N.map (Int.castRingHom ℂ)).PosSemidef := by
  have h1 := hA.conjTranspose_mul_mul_same (P.map (Int.castRingHom ℂ))
  have e1 : (P.map (Int.castRingHom ℂ))ᴴ * A.map (Int.castRingHom ℂ) *
      P.map (Int.castRingHom ℂ) = (((d : ℝ) ^ 2 : ℝ) : ℂ) • N.map (Int.castRingHom ℂ) := by
    rw [← certificateX2_int_map_transpose, ← Matrix.map_mul, ← Matrix.map_mul, hface]
    ext i j
    first
    | (simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom,
        Int.cast_mul, Int.cast_pow, Complex.ofReal_pow, Complex.ofReal_intCast]; done)
    | (simp [Matrix.map_apply, Matrix.smul_apply]; done)
    | (simp [Matrix.map_apply, Matrix.smul_apply]; ring)
  rw [e1] at h1
  have h2 := certificateX2_posSemidef_ofReal_smul h1
    (show (0 : ℝ) ≤ 1 / (d : ℝ) ^ 2 by positivity)
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have e2 : (((1 / (d : ℝ) ^ 2 : ℝ)) : ℂ) • ((((d : ℝ) ^ 2 : ℝ) : ℂ) •
      N.map (Int.castRingHom ℂ)) = N.map (Int.castRingHom ℂ) := by
    rw [smul_smul]
    have e3 : (((1 / (d : ℝ) ^ 2 : ℝ)) : ℂ) * (((d : ℝ) ^ 2 : ℝ) : ℂ) = 1 := by
      push_cast
      first
      | exact one_div_mul_cancel (pow_ne_zero 2 hd')
      | exact inv_mul_cancel₀ (pow_ne_zero 2 hd')
      | (field_simp; done)
    rw [e3, one_smul]
  rw [e2] at h2
  exact h2

end X2Psd

/-- Gram-form block families with nonnegative real weights. -/
theorem certificateX2_blocks_posSemidef_of_gram {ι : Type*} {d e : ι → Type*}
    [∀ b, Fintype (d b)] [∀ b, Fintype (e b)]
    (N : ∀ b, Matrix (d b) (d b) ℂ) (A : ∀ b, Matrix (d b) (e b) ℂ) (c : ι → ℝ)
    (hc : ∀ b, 0 ≤ c b) (hN : ∀ b, N b = (c b : ℂ) • (A b * (A b)ᴴ)) :
    ∀ b, (N b).PosSemidef := fun b => by
  rw [hN b]
  exact certificateX2_gram_posSemidef (A b) (hc b)

/-- BLOCK FORM FOR `qutritEndpointInequality_of_block_residual`: every block outside a set `S` is
a Gram form `c b • A b (A b)ᴴ` with `c b ≥ 0` (the untouched trial blocks, empty faces included
with `A b = 0`), and the blocks in `S` (the corrected ones) are positive by separate checks. -/
theorem certificateX2_blocks_posSemidef_of_gram_except {ι : Type*} {d e : ι → Type*}
    [∀ b, Fintype (d b)] [∀ b, Fintype (e b)] (S : Set ι)
    (N : ∀ b, Matrix (d b) (d b) ℂ) (A : ∀ b, Matrix (d b) (e b) ℂ) (c : ι → ℝ)
    (hc : ∀ b, b ∉ S → 0 ≤ c b) (hN : ∀ b, b ∉ S → N b = (c b : ℂ) • (A b * (A b)ᴴ))
    (hS : ∀ b, b ∈ S → (N b).PosSemidef) : ∀ b, (N b).PosSemidef := fun b => by
  by_cases h : b ∈ S
  · exact hS b h
  · rw [hN b h]
    exact certificateX2_gram_posSemidef (A b) (hc b h)

/-- Integer Gram blocks `(1/s b)² • (A b)(A b)ᵀ` (trial factors `K Z` or `Z`, scale `2^80`). -/
theorem certificateX2_int_blocks_posSemidef_of_gram {ι : Type*} {d e : ι → Type*}
    [∀ b, Fintype (d b)] [∀ b, Fintype (e b)]
    (N : ∀ b, Matrix (d b) (d b) ℂ) (A : ∀ b, Matrix (d b) (e b) ℤ) (s : ι → ℤ)
    (hN : ∀ b, N b = (1 / (s b : ℂ)) ^ 2 • (A b * (A b)ᵀ).map (Int.castRingHom ℂ)) :
    ∀ b, (N b).PosSemidef := fun b => by
  rw [hN b]
  exact certificateX2_int_gram_scaled_posSemidef (A b) (s b)

end ThreeCopyQutritWerner

end
