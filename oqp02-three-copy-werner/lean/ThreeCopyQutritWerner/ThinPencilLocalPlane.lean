module

public import ThreeCopyQutritWerner.JointPencilOneAnchor
public import ThreeCopyQutritWerner.ThinPencilJointSeparation

@[expose] public section


/-!
# Actual retained-site planes from a source anchor

Original input and output blocks with index two vanish in this branch.
The genuine opposite-total-line exception becomes a bound on the entire
original partner flattening, rather than a pointwise pencil assertion.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem firstSite_two_block_columns_mem
    (X : Matrix QutritSites (Fin 2) ℂ) (P : Submodule ℂ (Fin 3 → ℂ))
    (h2 : firstSiteFactorBlock X 2 = 0)
    (h0 : ∀ j, (twoSiteFactorFlatten (firstSiteFactorBlock X 0)).col j ∈ P)
    (h1 : ∀ j, (twoSiteFactorFlatten (firstSiteFactorBlock X 1)).col j ∈ P) :
    ∀ j, (coherentFlatten₂ X).col j ∈ P := by
  rintro ⟨⟨i, c⟩, k⟩
  fin_cases i
  · exact h0 (c, k)
  · exact h1 (c, k)
  · have he : (coherentFlatten₂ X).col ((2, c), k) = 0 := by
      ext b
      exact congrFun (congrFun h2 (b, c)) k
    change (coherentFlatten₂ X).col ((2, c), k) ∈ P
    rw [he]
    exact P.zero_mem

theorem matrix_rank_le_finrank_of_columns_mem
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (P : Submodule ℂ (m → ℂ)) (h : ∀ j, A.col j ∈ P) :
    A.rank ≤ Module.finrank ℂ P := by
  apply Submodule.finrank_mono
  rw [Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact h j

theorem thinFirstSite_local_plane_or_partner_line
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hX2 : firstSiteFactorBlock X 2 = 0) (hY2 : firstSiteFactorBlock Y 2 = 0)
    (hr : ∀ z w : ℂ, (twoSiteJointFactorFlatten
      (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1)
      (firstSiteFactorBlock Y 1 - w • firstSiteFactorBlock Y 0)).rank ≤ 2)
    (z₀ : ℂ) (hA : (twoSiteFactorFlatten
      (firstSiteFactorBlock X 0 + z₀ • firstSiteFactorBlock X 1)).rank = 2) :
    (∃ P : Submodule ℂ (Fin 3 → ℂ), Module.finrank ℂ P = 2 ∧
      (∀ j, (coherentFlatten₂ X).col j ∈ P) ∧
      (∀ j, (coherentFlatten₂ Y).col j ∈ P)) ∨
      (coherentFlatten₂ Y).rank ≤ 1 := by
  let A := twoSiteFactorFlatten (firstSiteFactorBlock X 0)
  let B := twoSiteFactorFlatten (firstSiteFactorBlock X 1)
  let C := twoSiteFactorFlatten (firstSiteFactorBlock Y 1)
  let D := -twoSiteFactorFlatten (firstSiteFactorBlock Y 0)
  have hr' (z w : ℂ) : (jointAffinePencil A B C D z w).rank ≤ 2 := by
    simpa only [sub_eq_add_neg, ← smul_neg, twoSiteJointFactorFlatten_affine,
      twoSiteFactorFlatten_neg] using hr z w
  have hA' : (A + z₀ • B).rank = 2 := hA
  rcases jointAffinePencil_common_plane_or_right_line A B C D hr' z₀ hA' with
    ⟨P, hP, ha, hb, hc, hd⟩ | hline
  · left
    refine ⟨P, hP, firstSite_two_block_columns_mem X P hX2 ha hb, ?_⟩
    apply firstSite_two_block_columns_mem Y P hY2 _ hc
    intro j
    have he := P.neg_mem (hd j)
    have hn : -D.col j = (twoSiteFactorFlatten (firstSiteFactorBlock Y 0)).col j := by
      ext i
      simp only [D, Pi.neg_apply, Matrix.col_apply, Matrix.neg_apply, neg_neg]
    exact hn ▸ he
  · right
    let P := LinearMap.range C.mulVecLin ⊔ LinearMap.range D.mulVecLin
    apply (matrix_rank_le_finrank_of_columns_mem (coherentFlatten₂ Y) P ?_).trans hline
    apply firstSite_two_block_columns_mem Y P hY2
    · intro j
      have hc : D.col j ∈ LinearMap.range D.mulVecLin := by
        rw [Matrix.range_mulVecLin]
        exact Submodule.subset_span ⟨j, rfl⟩
      have he := P.neg_mem (show D.col j ∈ P from (show LinearMap.range D.mulVecLin ≤ P from le_sup_right) hc)
      have hn : -D.col j = (twoSiteFactorFlatten (firstSiteFactorBlock Y 0)).col j := by
        ext i
        simp only [D, Pi.neg_apply, Matrix.col_apply, Matrix.neg_apply, neg_neg]
      exact hn ▸ he
    · intro j
      apply (show LinearMap.range C.mulVecLin ≤ P from le_sup_left)
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨j, rfl⟩

end ThreeCopyQutritWerner
