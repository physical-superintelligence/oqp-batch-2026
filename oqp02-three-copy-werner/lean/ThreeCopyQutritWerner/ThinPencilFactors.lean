module

public import ThreeCopyQutritWerner.ThinFirstSitePencil

@[expose] public section


/-!
# The actual affine source and conjugate-corange factors of the thin pencil

The original block pencil is the product of X₀+zX₁ with the adjoint of
Y₁−conj(z)Y₀. The conjugation is retained literally; no independent
source/corange parameters or common support are assumed here.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

def firstSiteFactorBlock {a d : Type*} (X : Matrix (a × d) (Fin 2) ℂ) (i : a) :
    Matrix d (Fin 2) ℂ := fun r j => X (i, r) j

theorem firstSiteBlock_mul_conjTranspose
    {a d : Type*} (X Y : Matrix (a × d) (Fin 2) ℂ) (i j : a) :
    firstSiteBlock (X * Yᴴ) i j = firstSiteFactorBlock X i * (firstSiteFactorBlock Y j)ᴴ := by
  ext r s
  rfl

theorem firstSiteFactor_quadratic_product
    {d : Type*} (X Y : Matrix (Fin 3 × d) (Fin 2) ℂ) (z : ℂ) :
    (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1) *
      (firstSiteFactorBlock Y 1 - conj z • firstSiteFactorBlock Y 0)ᴴ =
      firstSiteBlock (X * Yᴴ) 0 1 +
        z • (firstSiteBlock (X * Yᴴ) 1 1 - firstSiteBlock (X * Yᴴ) 0 0) -
        z ^ 2 • firstSiteBlock (X * Yᴴ) 1 0 := by
  ext r s
  simp [firstSiteFactorBlock, firstSiteBlock, Matrix.submatrix_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- Every actual affine-factor product is a cut zero; the original rank,
energy and missing output row supply the conclusion through the exact identity. -/
theorem thinFirstSite_affine_factor_rank_cut_zero
    {b c : Type*} [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]
    (X Y : Matrix (Fin 3 × b × c) (Fin 2) ℂ)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) (z : ℂ) :
    let T := (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1) *
      (firstSiteFactorBlock Y 1 - conj z • firstSiteFactorBlock Y 0)ᴴ
    T.rank ≤ 2 ∧ cutForm T = 0 := by
  dsimp only
  rw [firstSiteFactor_quadratic_product]
  exact thinFirstSite_quadratic_pencil_rank_cut_zero (X * Yᴴ) hC hz hrow z

end ThreeCopyQutritWerner
