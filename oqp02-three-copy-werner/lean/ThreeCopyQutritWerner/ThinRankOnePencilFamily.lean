module

public import ThreeCopyQutritWerner.ThinFixedRowFamily
public import ThreeCopyQutritWerner.ThinSingleSiteClassification

@[expose] public section


/-!
# Exhaustive classification of a rank-one retained-site source pencil

The two genuine affine-factor alternatives are treated separately. A common
column gives a local output ray, while a common row gives the actual
family-I projection on the other retained site.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem firstSite_pencil_common_column_single_output
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (u : Fin 3 → ℂ) (r s : Fin 3 × Fin 2 → ℂ) (hu : u ≠ 0)
    (h0 : twoSiteFactorFlatten (firstSiteFactorBlock X 0) = Matrix.vecMulVec u r)
    (h1 : twoSiteFactorFlatten (firstSiteFactorBlock X 1) = Matrix.vecMulVec u s)
    (h2 : firstSiteFactorBlock X 2 = 0) :
    HasSingleFirstOutput ((X * Yᴴ).submatrix siteEquiv₂ siteEquiv₂) := by
  let f : Fin 3 → Fin 3 × Fin 2 → ℂ := ![r, s, 0]
  have he (i b c : Fin 3) (j : Fin 2) : X (i, b, c) j = u b * f i (c, j) := by
    fin_cases i
    · exact congrFun (congrFun h0 b) (c, j)
    · exact congrFun (congrFun h1 b) (c, j)
    · simpa [f, firstSiteFactorBlock] using congrFun (congrFun h2 (b, c)) j
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, u b₀ ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hu (funext hn)
  refine ⟨b₀, fun b => u b / u b₀, div_self hb₀, ?_⟩
  intro b p q
  change (X * Yᴴ) (p.1, b, p.2) (q.2.1, q.1, q.2.2) =
    (u b / u b₀) * (X * Yᴴ) (p.1, b₀, p.2) (q.2.1, q.1, q.2.2)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hb₀]

theorem isQutritZeroFamilyMember_of_firstSite_rank_one_pencil
    (X Y : Matrix QutritSites (Fin 2) ℂ) (h2 : firstSiteFactorBlock X 2 = 0)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hN : frobSq (X * Yᴴ) = 1) (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0)
    (hr : ∀ z : ℂ, (twoSiteFactorFlatten
      (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1)).rank ≤ 1) :
    IsQutritZeroFamilyMember (X * Yᴴ) := by
  have hf (z : ℂ) : (twoSiteFactorFlatten (firstSiteFactorBlock X 0) +
      z • twoSiteFactorFlatten (firstSiteFactorBlock X 1)).rank ≤ 1 := hr z
  rcases affinePencil_rank_le_one_common_factor
      (twoSiteFactorFlatten (firstSiteFactorBlock X 0))
      (twoSiteFactorFlatten (firstSiteFactorBlock X 1)) hf with
    ⟨h0, h1⟩ | ⟨u, r, s, hu, h0, h1⟩ | ⟨r, u, v, _, h0, h1⟩
  · have hX : X = 0 := by
      ext ⟨i, b, c⟩ j
      fin_cases i
      · exact congrFun (congrFun h0 b) (c, j)
      · exact congrFun (congrFun h1 b) (c, j)
      · exact congrFun (congrFun h2 (b, c)) j
    simp [hX, frobSq] at hN
  · exact isQutritZeroFamilyMember_of_single_output_at_site (X * Yᴴ) hC hz hN 1
      (firstSite_pencil_common_column_single_output X Y u r s hu h0 h1 h2)
  · exact isQutritZeroFamilyMember_of_firstSite_fixed_row X Y u v r h0 h1 h2 hC hz hN hrow

end ThreeCopyQutritWerner
