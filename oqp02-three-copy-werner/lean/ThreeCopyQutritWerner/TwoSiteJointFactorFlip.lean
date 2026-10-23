module

public import ThreeCopyQutritWerner.TwoSiteJointFactorFlatten
public import ThreeCopyQutritWerner.TwoCutSwap

@[expose] public section


/-! The second physical local joint minors, with literal source row reindexing. -/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

def twoSiteFactorFlip {a b n : Type*} (X : Matrix (a × b) n ℂ) : Matrix (b × a) n ℂ :=
  X.submatrix (Equiv.prodComm b a) id

theorem twoSiteFactorFlip_product
    (X Y : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ) :
    twoSiteFactorFlip X * (twoSiteFactorFlip Y)ᴴ = twoCutSwap (X * Yᴴ) := by
  unfold twoSiteFactorFlip twoCutSwap
  rw [Matrix.conjTranspose_submatrix]
  exact Matrix.submatrix_mul_equiv X Yᴴ (Equiv.prodComm _ _)
    (Equiv.refl (Fin 2)) (Equiv.prodComm _ _)

theorem twoSiteFactorFlip_rank
    (X : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ) : (twoSiteFactorFlip X).rank = X.rank :=
  Matrix.rank_submatrix X (Equiv.prodComm _ _) (Equiv.refl (Fin 2))

theorem twoSiteFactorFlatten_affine
    {a b n : Type*} (X Y : Matrix (a × b) n ℂ) (z : ℂ) :
    twoSiteFactorFlatten (X + z • Y) = twoSiteFactorFlatten X + z • twoSiteFactorFlatten Y := rfl

/-- Both original physical retained sites have all joint source/corange
minors zero. The second site uses the actual tuple swap on both factors. -/
theorem twoSiteJointFactorFlatten_both_minors_zero
    (X Y : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ)
    (hX : X.rank = 2) (hY : Y.rank = 2) (hq : cutForm (X * Yᴴ) = 0) :
    (∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
      ((twoSiteJointFactorFlatten X Y).submatrix id cols).det = 0) ∧
    (∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
      ((twoSiteJointFactorFlatten (twoSiteFactorFlip X) (twoSiteFactorFlip Y)).submatrix id cols).det = 0) := by
  refine ⟨twoSiteJointFactorFlatten_minors_zero_of_cut_zero X Y hX hY hq, ?_⟩
  apply twoSiteJointFactorFlatten_minors_zero_of_cut_zero
    (twoSiteFactorFlip X) (twoSiteFactorFlip Y)
    ((twoSiteFactorFlip_rank X).trans hX) ((twoSiteFactorFlip_rank Y).trans hY)
  rw [twoSiteFactorFlip_product, (twoCutSwap_data (X * Yᴴ)).2.2, hq]

end ThreeCopyQutritWerner
