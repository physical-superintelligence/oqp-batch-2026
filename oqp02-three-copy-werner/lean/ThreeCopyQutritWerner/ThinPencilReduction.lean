module

public import ThreeCopyQutritWerner.ThinPencilAnchor
public import ThreeCopyQutritWerner.ThinPencilAllInputMinors
public import ThreeCopyQutritWerner.BalancedScalarFactors
public import ThreeCopyQutritWerner.RankOne

@[expose] public section


/-!
# Faithful original-factor reduction of a thin endpoint zero

The actual factors, their full column ranks, their balanced Gram matrices,
and the missing source block are constructed from the original matrix.
Either the scalar-plane branch is already classified or both retained sites
obey the separated joint rank bounds with every original input block.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

theorem firstSiteFactorBlock_zero_of_product_missing_row
    {a d : Type*} [Fintype a] [Fintype d]
    (X Y : Matrix (a × d) (Fin 2) ℂ) (hY : Y.rank = 2) (k : a)
    (hrow : ∀ r q, (X * Yᴴ) (k, r) q = 0) : firstSiteFactorBlock X k = 0 := by
  have hYH : Yᴴ.rank = 2 := by rw [Matrix.rank_conjTranspose, hY]
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_eq_two Yᴴ hYH
  have hm : firstSiteFactorBlock X k * Yᴴ = 0 := by
    ext r q
    exact hrow r q
  calc
    firstSiteFactorBlock X k = firstSiteFactorBlock X k * (Yᴴ * R) := by
      rw [hR, Matrix.mul_one]
    _ = (firstSiteFactorBlock X k * Yᴴ) * R := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hm, Matrix.zero_mul]

/-- An exhaustive reduction with only original rank, energy, norm and
missing-output-coordinate hypotheses. This is a support-gluing reduction,
not a claim that every resulting coefficient family has one common plane. -/
theorem thinFirstSite_family_or_full_factor_local_bounds
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1)
    (hrow : ∀ r q, C (2, r) q = 0) :
    IsQutritZeroFamilyMember C ∨
      ∃ X Y : Matrix QutritSites (Fin 2) ℂ,
        C = X * Yᴴ ∧ Xᴴ * X = Yᴴ * Y ∧ X.rank = 2 ∧ Y.rank = 2 ∧
        firstSiteFactorBlock X 2 = 0 ∧
        ∀ z w t : ℂ,
          let A := firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1
          let B := firstSiteFactorBlock Y 1 - w • firstSiteFactorBlock Y 0 +
            t • firstSiteFactorBlock Y 2
          (twoSiteJointFactorFlatten A B).rank ≤ 2 ∧
            (twoSiteJointFactorFlatten (twoSiteFactorFlip A) (twoSiteFactorFlip B)).rank ≤ 2 := by
  have hCne : C ≠ 0 := by
    intro he
    simp [he, frobSq] at hN
  have hr := rank_eq_two_of_endpointEnergy_eq_zero C hC hz hCne
  obtain ⟨X, Y, he, hG⟩ := exists_balanced_twoColumn_factors C hC
  have hrXY : (X * Yᴴ).rank = 2 := by simpa only [← he] using hr
  obtain ⟨hX, hYH⟩ := rank_eq_two_of_mul X Yᴴ hrXY
  have hY : Y.rank = 2 := by simpa only [Matrix.rank_conjTranspose] using hYH
  have hrowXY : ∀ r q, (X * Yᴴ) (2, r) q = 0 := by simpa only [← he] using hrow
  have hNXY : frobSq (X * Yᴴ) = 1 := by simpa only [← he] using hN
  have hzXY : endpointEnergy (X * Yᴴ) = 0 := by simpa only [← he] using hz
  rcases thinFirstSite_family_or_nonzero_free_pencil X Y hrXY.le hNXY hrowXY with hfam | ⟨z₀, t₀, hn⟩
  · left
    simpa only [he] using hfam
  · refine Or.inr ⟨X, Y, he, hG, hX, hY,
      firstSiteFactorBlock_zero_of_product_missing_row X Y hY 2 hrowXY, ?_⟩
    exact thinFirstSite_all_input_joint_rank_le_two X Y hrXY.le hzXY hrowXY z₀ t₀ hn

end ThreeCopyQutritWerner
