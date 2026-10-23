module

public import ThreeCopyQutritWerner.ThinFixedRowProjection
public import ThreeCopyQutritWerner.ThinDoubleOutputFamilyI

@[expose] public section


/-!
# The original family-I conclusion for a fixed-row local source pencil

The same active-site projection is recovered from all original input
blocks. Both inactive vectors remain unrestricted two-qutrit vectors.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem isQutritZeroFamilyMember_of_thin_tensor_source
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (κ : Fin 3 × Fin 3 → ℂ) (R : Matrix (Fin 3) (Fin 2) ℂ)
    (hX : X = thinTensorSource κ R) (hκ2 : ∀ b, κ (2, b) = 0)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hN : frobSq (X * Yᴴ) = 1) (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) :
    IsQutritZeroFamilyMember (X * Yᴴ) := by
  have hκ : κ ≠ 0 := by
    intro hk
    have he : X = 0 := by rw [hX]; ext p j; simp [thinTensorSource, hk]
    simp [he, frobSq] at hN
  obtain ⟨P, hP, hPP, hPr, hc⟩ :=
    thin_fixed_row_all_input_projection X Y κ R hX hκ hκ2 hC hz hrow
  choose α hα using hc
  obtain ⟨J, hJ, hPJ⟩ := qutrit_orthogonal_rank_two_projection_frame P hP hPP hPr
  let D := (X * Yᴴ).submatrix siteEquiv₃ siteEquiv₃
  let T : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
    fun p q => κ p * α q.1 q.2
  have hentry (p q : QutritSites) :
      (X * Yᴴ) p q = κ (p.1, p.2.1) *
        (R * (firstSiteFactorBlock (firstSiteFactorBlock Y q.1) q.2.1)ᴴ) p.2.2 q.2.2 := by
    rw [hX]
    simp only [Matrix.mul_apply, thinTensorSource, Matrix.conjTranspose_apply,
      firstSiteFactorBlock, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hD : D = (J * Jᴴ) ⊗ₖ T := by
    rw [← hPJ]
    ext p q
    change (X * Yᴴ) (p.2.1, p.2.2, p.1) (q.2.1, q.2.2, q.1) = P p.1 q.1 * T p.2 q.2
    rw [hentry, hα]
    simp only [T, Matrix.smul_apply, smul_eq_mul]
    ring
  have hDr : D.rank ≤ 2 := (Matrix.rank_submatrix (X * Yᴴ) siteEquiv₃ siteEquiv₃).trans_le hC
  have hDN : frobSq D = 1 := (frobSq_submatrix_equiv siteEquiv₃ (X * Yᴴ)).trans hN
  obtain ⟨χ, η, hχ, hη, hf⟩ := qutrit_scalar_plane_normalized_familyI D hDr hDN J hJ T hD
  obtain ⟨h₀, h₁, h₀₁⟩ := binaryPartition_two_column_orthonormal J hJ
  apply binaryPartition_familyI_placement_member (X * Yᴴ) 2 _ _ χ η h₀ h₁ h₀₁ hχ hη
  exact hf

theorem isQutritZeroFamilyMember_of_firstSite_fixed_row
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (u v : Fin 3 → ℂ) (r : Fin 3 × Fin 2 → ℂ)
    (h0 : twoSiteFactorFlatten (firstSiteFactorBlock X 0) = Matrix.vecMulVec u r)
    (h1 : twoSiteFactorFlatten (firstSiteFactorBlock X 1) = Matrix.vecMulVec v r)
    (h2 : firstSiteFactorBlock X 2 = 0)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hN : frobSq (X * Yᴴ) = 1) (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) :
    IsQutritZeroFamilyMember (X * Yᴴ) := by
  exact isQutritZeroFamilyMember_of_thin_tensor_source X Y
    (fun p => ![u, v, 0] p.1 p.2) (fun i j => r (i, j))
    (firstSite_fixed_row_source X u v r h0 h1 h2)
    (by intro b; simp) hC hz hN hrow

end ThreeCopyQutritWerner
