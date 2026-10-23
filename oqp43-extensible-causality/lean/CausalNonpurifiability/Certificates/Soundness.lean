module

public import Mathlib

@[expose] public section


/-!
# `CausalNonpurifiability.Certificates.Soundness`

Certificate soundness. Every positivity claim of the release is a
rational *identity* `A = L * diagonal d * Lᵀ` (LDL), `A = ∑ cᵢ • vᵢ vᵢᵀ` (Gram) or
`A = c • (Mᵀ * M)` (Hermitian square) with nonnegative rational scalars, and the
theorems here lift the identity to the complex image `A.map (algebraMap ℚ ℂ)`:

* `rational_ldl_sound` — nonnegative pivots ⇒ `PosSemidef`;
* `rational_ldl_posDef` — positive pivots and an invertible factor ⇒ `PosDef`
  (`rational_ldl_posDef_of_inverse` takes an explicit two-sided inverse witness);
* `gram_sound` — `∑ cᵢ vᵢ vᵢᵀ` with `cᵢ ≥ 0` ⇒ `PosSemidef`;
* `transpose_mul_self_sound` — `c • (Mᵀ M)` with `c ≥ 0` ⇒ `PosSemidef`;
* `vecMulVec_self_sound` — a single rank-one `v vᵀ` ⇒ `PosSemidef`;
* `diagonal_nonneg_sound` — a nonnegative rational diagonal ⇒ `PosSemidef`.

We lift identities, not the proposition "PSD over `ℚ`": that proposition changes its
quantified vector domain when moved to `ℂ`.

Manuscript anchors: `eq:positive-blocks`, `eq:Gram`, `eq:witness-rankone`.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix
open scoped ComplexOrder

/-! ### Scalars: rational casts inside `ℂ` -/

/-- The complex algebra map from `ℚ` is the rational cast. -/
lemma algebraMap_rat_complex (q : ℚ) : algebraMap ℚ ℂ q = (q : ℂ) := eq_ratCast _ q

/-- Complex conjugation fixes rational casts. -/
lemma star_ratCast_complex (q : ℚ) : star (q : ℂ) = (q : ℂ) := by
  rw [Complex.star_def]
  exact map_ratCast (starRingEnd ℂ) q

/-- `algebraMap ℚ ℂ` intertwines the (trivial) star of `ℚ` with complex conjugation. -/
lemma algebraMap_rat_complex_semiconj : Function.Semiconj (algebraMap ℚ ℂ) star star := by
  intro q
  rw [star_trivial, algebraMap_rat_complex, star_ratCast_complex]

lemma algebraMap_rat_complex_nonneg {q : ℚ} (hq : 0 ≤ q) : 0 ≤ algebraMap ℚ ℂ q := by
  rw [algebraMap_rat_complex, Complex.nonneg_iff]
  simp [hq]

lemma algebraMap_rat_complex_pos {q : ℚ} (hq : 0 < q) : 0 < algebraMap ℚ ℂ q := by
  rw [algebraMap_rat_complex, Complex.pos_iff]
  simp [hq]

/-! ### Transport of the certificate shape along `Matrix.map (algebraMap ℚ ℂ)` -/

/-- The complex image of a rational matrix is "real": its conjugate transpose is the image of
the transpose. -/
lemma conjTranspose_map_rat {ι κ : Type*} (A : Matrix ι κ ℚ) :
    (A.map (algebraMap ℚ ℂ))ᴴ = Aᵀ.map (algebraMap ℚ ℂ) := by
  rw [← conjTranspose_map _ algebraMap_rat_complex_semiconj,
    conjTranspose_eq_transpose_of_trivial]

/-- The complex image of an LDL product is the LDL product of the images, with the transpose
factor read as a conjugate transpose. -/
lemma map_ldl {ι κ : Type*} [Fintype κ] [DecidableEq κ] (L : Matrix ι κ ℚ) (d : κ → ℚ) :
    (L * diagonal d * Lᵀ).map (algebraMap ℚ ℂ)
      = L.map (algebraMap ℚ ℂ) * diagonal (fun i => algebraMap ℚ ℂ (d i))
          * (L.map (algebraMap ℚ ℂ))ᴴ := by
  rw [Matrix.map_mul, Matrix.map_mul, diagonal_map (map_zero _), conjTranspose_map_rat,
    transpose_map]

/-- Entry formula of an LDL product. -/
lemma ldl_apply {ι κ : Type*} [Fintype κ] [DecidableEq κ] (L : Matrix ι κ ℚ) (d : κ → ℚ)
    (i j : ι) : (L * diagonal d * Lᵀ) i j = ∑ k, L i k * d k * L j k := by
  rw [mul_apply]
  simp only [mul_diagonal, transpose_apply]

/-! ### LDL certificates -/

/-- **LDL soundness.** A rational matrix `A = L * diagonal d * Lᵀ` with nonnegative pivots has a
positive semidefinite complex image. -/
theorem rational_ldl_sound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℚ) (L : Matrix ι κ ℚ) (d : κ → ℚ)
    (hA : A = L * diagonal d * Lᵀ) (hd : ∀ i, 0 ≤ d i) :
    (A.map (algebraMap ℚ ℂ)).PosSemidef := by
  subst hA
  rw [map_ldl]
  exact (PosSemidef.diagonal fun i => algebraMap_rat_complex_nonneg (hd i)).mul_mul_conjTranspose_same _

/-- LDL soundness from the entry formula `A i j = ∑ k, L i k * d k * L j k`
(cheaper to check by `decide` than the matrix product). -/
theorem rational_ldl_sound_of_entries {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℚ) (L : Matrix ι κ ℚ) (d : κ → ℚ)
    (hA : ∀ i j, A i j = ∑ k, L i k * d k * L j k) (hd : ∀ i, 0 ≤ d i) :
    (A.map (algebraMap ℚ ℂ)).PosSemidef :=
  rational_ldl_sound A L d (Matrix.ext fun i j => by rw [hA, ldl_apply]) hd

/-- **LDL positive definiteness.** Strictly positive pivots and an invertible factor give a
positive definite complex image. -/
theorem rational_ldl_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A L : Matrix ι ι ℚ) (d : ι → ℚ)
    (hA : A = L * diagonal d * Lᵀ) (hd : ∀ i, 0 < d i) (hL : IsUnit L) :
    (A.map (algebraMap ℚ ℂ)).PosDef := by
  subst hA
  rw [map_ldl]
  refine (PosDef.diagonal fun i => algebraMap_rat_complex_pos (hd i)).mul_mul_conjTranspose_same ?_
  rw [vecMul_injective_iff_isUnit]
  simpa using hL.map (algebraMap ℚ ℂ).mapMatrix

/-- Positive definiteness from an explicit inverse witness `L * L' = 1` and the entry formula. -/
theorem rational_ldl_posDef_of_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A L L' : Matrix ι ι ℚ) (d : ι → ℚ)
    (hA : ∀ i j, A i j = ∑ k, L i k * d k * L j k) (hd : ∀ i, 0 < d i) (hL : L * L' = 1) :
    (A.map (algebraMap ℚ ℂ)).PosDef :=
  rational_ldl_posDef A L d (Matrix.ext fun i j => by rw [hA, ldl_apply]) hd
    ((isUnit_iff_isUnit_det L).mpr (isUnit_det_of_right_inverse hL))

/-! ### Gram and Hermitian-square certificates -/

/-- **Gram soundness.** `∑ i, cᵢ • vᵢ vᵢᵀ` with `cᵢ ≥ 0` has a PSD complex image (`eq:Gram`). -/
theorem gram_sound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℚ) (c : κ → ℚ) (v : κ → ι → ℚ)
    (hA : A = ∑ k, c k • vecMulVec (v k) (v k)) (hc : ∀ k, 0 ≤ c k) :
    (A.map (algebraMap ℚ ℂ)).PosSemidef := by
  refine rational_ldl_sound A (of fun i k => v k i) c ?_ hc
  ext i j
  rw [hA, ldl_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, of_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- A single rational rank-one square `v vᵀ` has a PSD complex image (`eq:witness-rankone`). -/
theorem vecMulVec_self_sound {ι : Type*} [Fintype ι] (v : ι → ℚ) :
    ((vecMulVec v v).map (algebraMap ℚ ℂ)).PosSemidef := by
  refine gram_sound (vecMulVec v v) (fun _ : Fin 1 => (1 : ℚ)) (fun _ => v) ?_ (fun _ => zero_le_one)
  simp

/-- **Hermitian squares.** `c • (Mᵀ * M)` with `c ≥ 0` has a PSD complex image
(used for `U = (Π+G_A)ᵀ(Π+G_A)/40`). -/
theorem transpose_mul_self_sound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℚ) (M : Matrix κ ι ℚ) (c : ℚ) (hA : A = c • (Mᵀ * M)) (hc : 0 ≤ c) :
    (A.map (algebraMap ℚ ℂ)).PosSemidef := by
  refine rational_ldl_sound A Mᵀ (fun _ => c) ?_ (fun _ => hc)
  rw [hA, transpose_transpose, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul]

/-- A nonnegative rational diagonal has a PSD complex image. -/
theorem diagonal_nonneg_sound {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℚ)
    (hf : ∀ i, 0 ≤ f i) : ((diagonal f).map (algebraMap ℚ ℂ)).PosSemidef := by
  rw [diagonal_map (map_zero _)]
  exact PosSemidef.diagonal fun i => algebraMap_rat_complex_nonneg (hf i)

/-- A positive rational diagonal has a positive definite complex image. -/
theorem diagonal_pos_sound {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℚ)
    (hf : ∀ i, 0 < f i) : ((diagonal f).map (algebraMap ℚ ℂ)).PosDef := by
  rw [diagonal_map (map_zero _)]
  exact PosDef.diagonal fun i => algebraMap_rat_complex_pos (hf i)

/-- The complex image of a symmetric rational matrix is Hermitian. -/
theorem isHermitian_map_of_transpose {ι : Type*} (A : Matrix ι ι ℚ) (hA : Aᵀ = A) :
    (A.map (algebraMap ℚ ℂ)).IsHermitian := by
  rw [IsHermitian, conjTranspose_map_rat, hA]

end CausalNonpurifiability
