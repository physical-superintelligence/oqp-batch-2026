module

public import ThreeCopyQutritWerner.ThinFirstSiteFreeInput
public import ThreeCopyQutritWerner.ThinPencilFactors

@[expose] public section


/-!
# Literal thin factor pencils retaining all input blocks

The free parameter multiplies the original third input factor. The
orthogonal input ray has its conjugate coefficient, so its adjoint gives
exactly the displayed source/corange product.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

theorem firstSiteFactor_free_input_product
    {d : Type*} [Fintype d] [DecidableEq d]
    (X Y : Matrix (Fin 3 × d) (Fin 2) ℂ) (z t : ℂ) :
    (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1) *
      (firstSiteFactorBlock Y 1 - conj z • firstSiteFactorBlock Y 0 +
        t • firstSiteFactorBlock Y 2)ᴴ =
      firstSiteContraction (X * Yᴴ) ![1, conj z, 0] ![-z, 1, conj t] := by
  ext r s
  simp [firstSiteContraction_apply, firstSiteFactorBlock, Matrix.mul_apply,
    Fin.sum_univ_three, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- The original zero supplies rank and cut zero for every complex free
input coefficient, not only for the binary input restriction. -/
theorem thinFirstSite_free_input_factor_rank_cut_zero
    {b c : Type*} [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]
    (X Y : Matrix (Fin 3 × b × c) (Fin 2) ℂ)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) (z t : ℂ) :
    let T := (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1) *
      (firstSiteFactorBlock Y 1 - conj z • firstSiteFactorBlock Y 0 +
        t • firstSiteFactorBlock Y 2)ᴴ
    T.rank ≤ 2 ∧ cutForm T = 0 := by
  dsimp only
  rw [firstSiteFactor_free_input_product]
  refine ⟨(firstSiteContraction_rank_le _ _ _).trans hC, ?_⟩
  apply firstSiteContraction_cutForm_zero_of_thin_orthogonal_free_input
    (X * Yᴴ) hC hz hrow
  · simp [braket, Fin.sum_univ_three]
  · simp

end ThreeCopyQutritWerner
