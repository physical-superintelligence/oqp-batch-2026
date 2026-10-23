module

public import ThreeCopyQutritWerner.JointPencilSupport
public import ThreeCopyQutritWerner.AffinePencilRankDrop

@[expose] public section


/-!
# A common plane or an opposite range line from one actual anchor

One rank-two member traps both coefficients of the opposite family in its
plane. If those opposite coefficients span a plane, all rank-two members of
the first pencil have that same plane. Two distinct such members, obtained
from the proved finite rank-drop set, recover both first coefficients.

This retains the necessary opposite-range-line exception. With no anchor on
either side a fixed-row-factor pencil can have varying range.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

variable {κ η : Type*} [Fintype κ] [Fintype η]

private theorem oneAnchor_col_mem_range {ι : Type*} [Fintype ι]
    (A : Matrix (Fin 3) ι ℂ) (j : ι) : A.col j ∈ LinearMap.range A.mulVecLin := by
  rw [Matrix.range_mulVecLin]
  exact Submodule.subset_span ⟨j, rfl⟩

/-- One actual left rank-two member contains both right coefficient ranges. -/
theorem jointAffinePencil_right_coefficients_le_anchor
    (A B : Matrix (Fin 3) κ ℂ) (C D : Matrix (Fin 3) η ℂ)
    (hr : ∀ z w : ℂ, (jointAffinePencil A B C D z w).rank ≤ 2)
    (z₀ : ℂ) (hA : (A + z₀ • B).rank = 2) :
    LinearMap.range C.mulVecLin ⊔ LinearMap.range D.mulVecLin ≤
      LinearMap.range (A + z₀ • B).mulVecLin := by
  let E := LinearMap.range (A + z₀ • B).mulVecLin
  have he (w : ℂ) : E = LinearMap.range (jointAffinePencil A B C D z₀ w).mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_le
      (jointAffinePencil_left_range_le A B C D z₀ w)
    change (jointAffinePencil A B C D z₀ w).rank ≤ (A + z₀ • B).rank
    rw [hA]
    exact hr z₀ w
  have hy (w : ℂ) : LinearMap.range (C + w • D).mulVecLin ≤ E := by
    rw [he w]
    exact jointAffinePencil_right_range_le A B C D z₀ w
  have hc (j : η) : C.col j ∈ E := by
    simpa only [zero_smul, add_zero] using hy 0 (oneAnchor_col_mem_range (C + (0 : ℂ) • D) j)
  have hd (j : η) : D.col j ∈ E := by
    have h := E.sub_mem (hy 1 (oneAnchor_col_mem_range (C + (1 : ℂ) • D) j)) (hc j)
    have he : (C + (1 : ℂ) • D).col j - C.col j = D.col j := by
      funext i
      change C i j + 1 * D i j - C i j = D i j
      ring
    exact he ▸ h
  apply sup_le
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hc j
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hd j

/-- A single rank-two anchor suffices unless the entire opposite coefficient
range is at most one-dimensional. No second pointwise anchor is required. -/
theorem jointAffinePencil_common_plane_or_right_line
    (A B : Matrix (Fin 3) κ ℂ) (C D : Matrix (Fin 3) η ℂ)
    (hr : ∀ z w : ℂ, (jointAffinePencil A B C D z w).rank ≤ 2)
    (z₀ : ℂ) (hA : (A + z₀ • B).rank = 2) :
    (∃ E : Submodule ℂ (Fin 3 → ℂ), Module.finrank ℂ E = 2 ∧
      (∀ j, A.col j ∈ E) ∧ (∀ j, B.col j ∈ E) ∧
      (∀ j, C.col j ∈ E) ∧ (∀ j, D.col j ∈ E)) ∨
    Module.finrank ℂ (LinearMap.range C.mulVecLin ⊔ LinearMap.range D.mulVecLin : Submodule ℂ (Fin 3 → ℂ)) ≤ 1 := by
  classical
  let E : Submodule ℂ (Fin 3 → ℂ) :=
    LinearMap.range C.mulVecLin ⊔ LinearMap.range D.mulVecLin
  by_cases hsmall : Module.finrank ℂ E ≤ 1
  · exact Or.inr hsmall
  have hle0 : E ≤ LinearMap.range (A + z₀ • B).mulVecLin :=
    jointAffinePencil_right_coefficients_le_anchor A B C D hr z₀ hA
  have hE : Module.finrank ℂ E = 2 := by
    have h := Submodule.finrank_mono hle0
    change Module.finrank ℂ E ≤ (A + z₀ • B).rank at h
    omega
  have he (z : ℂ) (hz : (A + z • B).rank = 2) :
      E = LinearMap.range (A + z • B).mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_le
      (jointAffinePencil_right_coefficients_le_anchor A B C D hr z hz)
    change (A + z • B).rank ≤ Module.finrank ℂ E
    omega
  have hbnd (z : ℂ) : (A + z • B).rank ≤ 2 := by
    exact (Submodule.finrank_mono
      (jointAffinePencil_left_range_le A B C D z 0)).trans (hr z 0)
  obtain ⟨z₁, hz₁⟩ := ((affinePencil_rank_drop_finite A B z₀ hA.ge).insert z₀).exists_notMem
  have hz₁ne : z₁ ≠ z₀ := by
    intro h
    exact hz₁ (Set.mem_insert_iff.mpr (Or.inl h))
  have hz₁rank : ¬ (A + z₁ • B).rank < 2 := by
    intro h
    exact hz₁ (Set.mem_insert_of_mem _ h)
  have hA₁ : (A + z₁ • B).rank = 2 :=
    le_antisymm (hbnd z₁) (Nat.le_of_not_gt hz₁rank)
  have h0 (j : κ) : (A + z₀ • B).col j ∈ E := by
    rw [he z₀ hA]
    exact oneAnchor_col_mem_range _ j
  have h1 (j : κ) : (A + z₁ • B).col j ∈ E := by
    rw [he z₁ hA₁]
    exact oneAnchor_col_mem_range _ j
  have hB (j : κ) : B.col j ∈ E := by
    have hcol : B.col j = (z₁ - z₀)⁻¹ •
        ((A + z₁ • B).col j - (A + z₀ • B).col j) := by
      ext i
      change B i j = (z₁ - z₀)⁻¹ *
        ((A i j + z₁ * B i j) - (A i j + z₀ * B i j))
      have hu := inv_mul_cancel₀ (sub_ne_zero.mpr hz₁ne)
      linear_combination -(B i j) * hu
    rw [hcol]
    exact E.smul_mem _ (E.sub_mem (h1 j) (h0 j))
  have hAc (j : κ) : A.col j ∈ E := by
    have hcol : A.col j = (A + z₀ • B).col j - z₀ • B.col j := by
      ext i
      change A i j = (A i j + z₀ * B i j) - z₀ * B i j
      ring
    rw [hcol]
    exact E.sub_mem (h0 j) (E.smul_mem _ (hB j))
  refine Or.inl ⟨E, hE, hAc, hB, ?_, ?_⟩
  · intro j
    exact (show LinearMap.range C.mulVecLin ≤ E from le_sup_left)
      (oneAnchor_col_mem_range C j)
  · intro j
    exact (show LinearMap.range D.mulVecLin ≤ E from le_sup_right)
      (oneAnchor_col_mem_range D j)

end ThreeCopyQutritWerner
