module

public import ThreeCopyQutritWerner.ThinPencilReduction

@[expose] public section


/-!
# The actual off-plane corange factor

Every source-pencil member paired with the original third input factor
is a cut zero. If this factor is nonzero, the full original source rank
forces its rank to be two; lower rank would annihilate every original block.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

theorem firstSiteFactor_offplane_product
    {d : Type*} [Fintype d] [DecidableEq d]
    (X Y : Matrix (Fin 3 × d) (Fin 2) ℂ) (z : ℂ) :
    (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1) *
      (firstSiteFactorBlock Y 2)ᴴ =
      firstSiteContraction (X * Yᴴ) ![1, conj z, 0] ![0, 0, 1] := by
  ext r s
  simp [firstSiteContraction_apply, firstSiteFactorBlock, Matrix.mul_apply,
    Fin.sum_univ_three, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem thinFirstSite_offplane_factor_rank_cut_zero
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) (z : ℂ) :
    let T := (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1) *
      (firstSiteFactorBlock Y 2)ᴴ
    T.rank ≤ 2 ∧ cutForm T = 0 := by
  dsimp only
  rw [firstSiteFactor_offplane_product]
  exact ⟨(firstSiteContraction_rank_le _ _ _).trans hC,
    firstSiteContraction_offplane_cutForm_zero (X * Yᴴ) hC hz hrow
      ![1, conj z, 0] (by simp)⟩

theorem thinFirstSite_offplane_factor_rank_two_of_nonzero
    (X Y : Matrix QutritSites (Fin 2) ℂ) (hX : X.rank = 2)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0)
    (hne : firstSiteFactorBlock Y 2 ≠ 0) : (firstSiteFactorBlock Y 2).rank = 2 := by
  have hbound : (firstSiteFactorBlock Y 2).rank ≤ 2 := by
    simpa using Matrix.rank_le_card_width (firstSiteFactorBlock Y 2)
  by_contra hnot
  have hsmall : (firstSiteFactorBlock Y 2).rank ≤ 1 := by omega
  have hb (i : Fin 3) : firstSiteBlock (X * Yᴴ) i 2 = 0 := by
    have hbr : (firstSiteBlock (X * Yᴴ) i 2).rank ≤ 1 := by
      rw [firstSiteBlock_mul_conjTranspose]
      exact (Matrix.rank_mul_le_right _ _).trans (by
        simpa only [Matrix.rank_conjTranspose] using hsmall)
    by_contra hn
    have ht := rank_two_of_nonzero_cutForm_zero _ (hbr.trans (by decide))
      (firstSiteBlock_cutForm_zero_of_thin_endpoint_zero (X * Yᴴ) hC hz 2 hrow i) hn
    omega
  have hp : X * (firstSiteFactorBlock Y 2)ᴴ = 0 := by
    ext ⟨i, r⟩ s
    exact congrFun (congrFun (hb i) r) s
  obtain ⟨L, hL⟩ := exists_left_inverse_of_rank_eq_two X hX
  have he : (firstSiteFactorBlock Y 2)ᴴ = 0 := by
    calc
      (firstSiteFactorBlock Y 2)ᴴ = (L * X) * (firstSiteFactorBlock Y 2)ᴴ := by
        rw [hL, Matrix.one_mul]
      _ = L * (X * (firstSiteFactorBlock Y 2)ᴴ) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hp, Matrix.mul_zero]
  apply hne
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] using
    congrArg Matrix.conjTranspose he

end ThreeCopyQutritWerner
