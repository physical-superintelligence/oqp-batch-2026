module

public import ThreeCopyQutritWerner.ThinPencilFactors
public import ThreeCopyQutritWerner.TwoCutFixedSourceCoordinates
public import ThreeCopyQutritWerner.ZeroRelations

@[expose] public section


/-!
# A scalar line of original source blocks is a single physical output ray

The coefficients include their literal conjugation when obtained by
cancelling a common full-column-rank left factor in the adjoint products.
No local output support is assumed in the conclusions.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem firstSiteFactor_blocks_line_single_output
    {a d : Type*} (X Y : Matrix (a × d) (Fin 2) ℂ) (k : a)
    (h : ∀ i, ∃ z : ℂ, firstSiteFactorBlock X i = z • firstSiteFactorBlock X k) :
    HasSingleFirstOutput (X * Yᴴ) := by
  classical
  refine ⟨k, fun i => if i = k then 1 else Classical.choose (h i), by simp, ?_⟩
  intro i r q
  by_cases hi : i = k
  · subst i
    simp
  · change (X * Yᴴ) (i, r) q =
      (if i = k then 1 else Classical.choose (h i)) * (X * Yᴴ) (k, r) q
    rw [if_neg hi]
    change (firstSiteFactorBlock X i * Yᴴ) r q =
      Classical.choose (h i) * (firstSiteFactorBlock X k * Yᴴ) r q
    have hc := congrArg (fun A : Matrix d (Fin 2) ℂ => (A * Yᴴ) r q)
      (Classical.choose_spec (h i))
    simpa only [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] using hc

theorem firstSiteFactor_adjoint_products_line_single_output
    {a d : Type*} [Fintype d]
    (X Y : Matrix (a × d) (Fin 2) ℂ) (Z : Matrix d (Fin 2) ℂ)
    (hZ : Z.rank = 2) (k : a)
    (h : ∀ i, ∃ z : ℂ,
      Z * (firstSiteFactorBlock X i)ᴴ = z • (Z * (firstSiteFactorBlock X k)ᴴ)) :
    HasSingleFirstOutput (X * Yᴴ) := by
  obtain ⟨L, hL⟩ := exists_left_inverse_of_rank_eq_two Z hZ
  apply firstSiteFactor_blocks_line_single_output X Y k
  intro i
  obtain ⟨z, hz⟩ := h i
  have he : (firstSiteFactorBlock X i)ᴴ = z • (firstSiteFactorBlock X k)ᴴ := by
    calc
      (firstSiteFactorBlock X i)ᴴ = (L * Z) * (firstSiteFactorBlock X i)ᴴ := by
        rw [hL, Matrix.one_mul]
      _ = L * (Z * (firstSiteFactorBlock X i)ᴴ) := Matrix.mul_assoc _ _ _
      _ = L * (z • (Z * (firstSiteFactorBlock X k)ᴴ)) := by rw [hz]
      _ = z • (firstSiteFactorBlock X k)ᴴ := by
        rw [Matrix.mul_smul, ← Matrix.mul_assoc, hL, Matrix.one_mul]
  refine ⟨star z, ?_⟩
  simpa only [Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose] using
    congrArg Matrix.conjTranspose he

end ThreeCopyQutritWerner
