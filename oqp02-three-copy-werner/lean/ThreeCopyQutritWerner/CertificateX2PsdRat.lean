module

public import ThreeCopyQutritWerner.CertificateX2Psd
public import Mathlib.Data.Rat.Cast.CharZero

@[expose] public section


/-!
# Positivity facts in the rational form

The reduced statement `X2ReducedBridge` (CertificateX2Reduced) takes rational
blocks `M : Matrix _ _ ℚ` and asks for `(x2Complex M).PosSemidef`, where
`x2Complex M = M.map (fun q : ℚ => (q : ℂ))`. Every statement below is written with that exact
cast, so it applies to `x2Complex M` by unfolding the definition:

* source blocks (sectors m, a; coefficient matrices in `J` coordinates): Gram forms
  `c • A Aᵀ` (`c ≥ 0`), in particular the trial `K Z Zᵀ Kᵀ / 2^160`
  (`certificateX2_rat_int_gram_posSemidef`), block families outside the corrected set
  (`certificateX2_rat_blocks_posSemidef_of_gram_except`), and congruences `B M Bᵀ` of a positive
  face block (`certificateX2_rat_congr_posSemidef`; corrected blocks `K (ZZᵀ/2^160 + C_b) Kᵀ`);
* residual blocks (sector h, quadratic-form coordinates): rational blocks with integer
  numerators `(1/den) • N` (`certificateX2_rat_int_div_posSemidef`), `N` proved positive by the
  generated per-block modules.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

section X2PsdRat

variable {n k m : Type*} [Fintype n] [Fintype k] [Fintype m]

/-- The complex cast of a rational transpose is the conjugate transpose of the cast. -/
theorem certificateX2_rat_map_transpose (A : Matrix n k ℚ) :
    Aᵀ.map (fun q : ℚ => (q : ℂ)) = (A.map (fun q : ℚ => (q : ℂ)))ᴴ := by
  ext i j
  first
  | (simp [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]; done)
  | (simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
      star_ratCast]; done)

/-- The complex cast of a rational product. -/
theorem certificateX2_rat_map_mul (A : Matrix n k ℚ) (B : Matrix k m ℚ) :
    (A * B).map (fun q : ℚ => (q : ℂ)) =
      A.map (fun q : ℚ => (q : ℂ)) * B.map (fun q : ℚ => (q : ℂ)) := by
  first
  | exact Matrix.map_mul (f := Rat.castHom ℂ)
  | (rw [show (fun q : ℚ => (q : ℂ)) = ⇑(Rat.castHom ℂ) from rfl]; exact Matrix.map_mul)
  | (ext i j; simp [Matrix.mul_apply, Matrix.map_apply]; done)

/-- Rational Gram forms are positive semidefinite after the complex cast. -/
theorem certificateX2_rat_gram_posSemidef (A : Matrix n k ℚ) :
    ((A * Aᵀ).map (fun q : ℚ => (q : ℂ))).PosSemidef := by
  rw [certificateX2_rat_map_mul, certificateX2_rat_map_transpose]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Nonnegative rational multiples preserve positivity after the complex cast. -/
theorem certificateX2_rat_smul_posSemidef {M : Matrix n n ℚ}
    (hM : (M.map (fun q : ℚ => (q : ℂ))).PosSemidef) {c : ℚ} (hc : 0 ≤ c) :
    ((c • M).map (fun q : ℚ => (q : ℂ))).PosSemidef := by
  have e : (c • M).map (fun q : ℚ => (q : ℂ)) =
      (((c : ℝ) : ℂ)) • M.map (fun q : ℚ => (q : ℂ)) := by
    ext i j
    first
    | (simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Rat.cast_mul,
        Complex.ofReal_ratCast]; done)
    | (simp [Matrix.map_apply, Matrix.smul_apply]; done)
  rw [e]
  exact certificateX2_posSemidef_ofReal_smul hM (by exact_mod_cast hc)

/-- Congruence: a positive face block `M` gives a positive block `B M Bᵀ` (for instance the
corrected source block `K (Z Zᵀ / 2^160 + C_b) Kᵀ` in `J` coordinates). -/
theorem certificateX2_rat_congr_posSemidef (M : Matrix n n ℚ) (B : Matrix m n ℚ)
    (hM : (M.map (fun q : ℚ => (q : ℂ))).PosSemidef) :
    ((B * M * Bᵀ).map (fun q : ℚ => (q : ℂ))).PosSemidef := by
  rw [certificateX2_rat_map_mul, certificateX2_rat_map_mul, certificateX2_rat_map_transpose]
  exact hM.mul_mul_conjTranspose_same _

/-- Integer numerators: the rational cast followed by the complex cast is the integer cast. -/
theorem certificateX2_rat_of_int_map (N : Matrix n m ℤ) :
    (N.map (Int.cast : ℤ → ℚ)).map (fun q : ℚ => (q : ℂ)) = N.map (Int.castRingHom ℂ) := by
  ext i j
  first
  | (simp only [Matrix.map_apply, Int.coe_castRingHom, Rat.cast_intCast]; done)
  | (simp [Matrix.map_apply]; done)

/-- RESIDUAL BLOCKS: rational blocks `(1/den) • N` with integer numerators `N ⪰ 0`. -/
theorem certificateX2_rat_int_div_posSemidef (N : Matrix n n ℤ) (den : ℤ) (hden : 0 < den)
    (hN : (N.map (Int.castRingHom ℂ)).PosSemidef) :
    (((1 / (den : ℚ)) • N.map (Int.cast : ℤ → ℚ)).map (fun q : ℚ => (q : ℂ))).PosSemidef := by
  have h0 : (0 : ℚ) < (den : ℚ) := by exact_mod_cast hden
  apply certificateX2_rat_smul_posSemidef
  · rw [certificateX2_rat_of_int_map]
    exact hN
  · exact div_nonneg zero_le_one h0.le

/-- TRIAL SOURCE BLOCKS: `(1/s)² • (A Aᵀ)` with an integer factor `A` (`A = K Z`, `s = 2^80`). -/
theorem certificateX2_rat_int_gram_posSemidef (A : Matrix n k ℤ) (s : ℤ) :
    (((1 / (s : ℚ)) ^ 2 • (A * Aᵀ).map (Int.cast : ℤ → ℚ)).map
      (fun q : ℚ => (q : ℂ))).PosSemidef := by
  apply certificateX2_rat_smul_posSemidef
  · rw [certificateX2_rat_of_int_map]
    exact certificateX2_int_gram_posSemidef A
  · positivity

end X2PsdRat

/-- Source block families (in the bridge's form): every block outside a set `S` of corrected
blocks is a Gram form `c b • A b (A b)ᵀ` with `c b ≥ 0`; the blocks in `S` are positive by
separate checks. Applies to `∀ b, (x2Complex (Nm b)).PosSemidef` by unfolding `x2Complex`. -/
theorem certificateX2_rat_blocks_posSemidef_of_gram_except {ι : Type*} {d e : ι → Type*}
    [∀ b, Fintype (d b)] [∀ b, Fintype (e b)] (S : Set ι)
    (N : ∀ b, Matrix (d b) (d b) ℚ) (A : ∀ b, Matrix (d b) (e b) ℚ) (c : ι → ℚ)
    (hc : ∀ b, b ∉ S → 0 ≤ c b) (hN : ∀ b, b ∉ S → N b = c b • (A b * (A b)ᵀ))
    (hS : ∀ b, b ∈ S → ((N b).map (fun q : ℚ => (q : ℂ))).PosSemidef) :
    ∀ b, ((N b).map (fun q : ℚ => (q : ℂ))).PosSemidef := fun b => by
  by_cases h : b ∈ S
  · exact hS b h
  · rw [hN b h]
    exact certificateX2_rat_smul_posSemidef (certificateX2_rat_gram_posSemidef (A b)) (hc b h)

/-- Trial source block families with integer factors `A b = K_b Z_b` and scale `s b = 2^80`. -/
theorem certificateX2_rat_int_blocks_posSemidef_of_gram_except {ι : Type*} {d e : ι → Type*}
    [∀ b, Fintype (d b)] [∀ b, Fintype (e b)] (S : Set ι)
    (N : ∀ b, Matrix (d b) (d b) ℚ) (A : ∀ b, Matrix (d b) (e b) ℤ) (s : ι → ℤ)
    (hN : ∀ b, b ∉ S → N b = (1 / (s b : ℚ)) ^ 2 • (A b * (A b)ᵀ).map (Int.cast : ℤ → ℚ))
    (hS : ∀ b, b ∈ S → ((N b).map (fun q : ℚ => (q : ℂ))).PosSemidef) :
    ∀ b, ((N b).map (fun q : ℚ => (q : ℂ))).PosSemidef := fun b => by
  by_cases h : b ∈ S
  · exact hS b h
  · rw [hN b h]
    exact certificateX2_rat_int_gram_posSemidef (A b) (s b)

end ThreeCopyQutritWerner

end
