module

public import ThreeCopyQutritWerner.ComplexConjugatePolynomialDense
public import ThreeCopyQutritWerner.CoherentPencilSupport

@[expose] public section


/-!
# One actual plane from two rank-two affine anchors

The joint minors give a rank bound for every independent pair of parameters.
An actual rank-two member of each family then fixes one common plane for
all four coefficient matrices. Both anchors are explicit; degenerate
rank-one families are a separate classification branch.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {κ ν : Type*} [Fintype κ] [Fintype ν]

theorem jointAffinePencil_left_range_le
    (A B : Matrix (Fin 3) κ ℂ) (C D : Matrix (Fin 3) ν ℂ) (z w : ℂ) :
    LinearMap.range (A + z • B).mulVecLin ≤
      LinearMap.range (jointAffinePencil A B C D z w).mulVecLin := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨Sum.inl j, rfl⟩

theorem jointAffinePencil_right_range_le
    (A B : Matrix (Fin 3) κ ℂ) (C D : Matrix (Fin 3) ν ℂ) (z w : ℂ) :
    LinearMap.range (C + w • D).mulVecLin ≤
      LinearMap.range (jointAffinePencil A B C D z w).mulVecLin := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨Sum.inr j, rfl⟩

private theorem plane_eq_of_le_rank_two
    (P Q : Submodule ℂ (Fin 3 → ℂ)) (h : P ≤ Q)
    (hP : Module.finrank ℂ P = 2) (hQ : Module.finrank ℂ Q ≤ 2) : P = Q :=
  Submodule.eq_of_le_of_finrank_le h (by omega)

private theorem matrix_col_mem_range {ι : Type*} [Fintype ι]
    (A : Matrix (Fin 3) ι ℂ) (j : ι) : A.col j ∈ LinearMap.range A.mulVecLin := by
  rw [Matrix.range_mulVecLin]
  exact Submodule.subset_span ⟨j, rfl⟩

/-- Two actual rank-two anchors construct one common two-dimensional
submodule containing every original coefficient column. -/
theorem jointAffinePencil_common_plane_of_two_anchors
    (A B : Matrix (Fin 3) κ ℂ) (C D : Matrix (Fin 3) ν ℂ)
    (hr : ∀ z w : ℂ, (jointAffinePencil A B C D z w).rank ≤ 2)
    (z₀ w₀ : ℂ) (hA : (A + z₀ • B).rank = 2) (hC : (C + w₀ • D).rank = 2) :
    ∃ E : Submodule ℂ (Fin 3 → ℂ), Module.finrank ℂ E = 2 ∧
      (∀ j, A.col j ∈ E) ∧ (∀ j, B.col j ∈ E) ∧
      (∀ j, C.col j ∈ E) ∧ (∀ j, D.col j ∈ E) := by
  let E := LinearMap.range (A + z₀ • B).mulVecLin
  have hE : Module.finrank ℂ E = 2 := hA
  have hleft (w : ℂ) : E = LinearMap.range (jointAffinePencil A B C D z₀ w).mulVecLin :=
    plane_eq_of_le_rank_two _ _ (jointAffinePencil_left_range_le A B C D z₀ w) hE (hr z₀ w)
  have hY (w : ℂ) : LinearMap.range (C + w • D).mulVecLin ≤ E := by
    rw [hleft w]
    exact jointAffinePencil_right_range_le A B C D z₀ w
  have hYE : LinearMap.range (C + w₀ • D).mulVecLin = E :=
    plane_eq_of_le_rank_two _ _ (hY w₀) hC hE.le
  have hright (z : ℂ) : LinearMap.range (C + w₀ • D).mulVecLin =
      LinearMap.range (jointAffinePencil A B C D z w₀).mulVecLin :=
    plane_eq_of_le_rank_two _ _ (jointAffinePencil_right_range_le A B C D z w₀) hC (hr z w₀)
  have hX (z : ℂ) : LinearMap.range (A + z • B).mulVecLin ≤ E := by
    rw [← hYE, hright z]
    exact jointAffinePencil_left_range_le A B C D z w₀
  have hAc (j : κ) : A.col j ∈ E := by
    simpa only [zero_smul, add_zero] using hX 0 (matrix_col_mem_range (A + (0 : ℂ) • B) j)
  have hCc (j : ν) : C.col j ∈ E := by
    simpa only [zero_smul, add_zero] using hY 0 (matrix_col_mem_range (C + (0 : ℂ) • D) j)
  refine ⟨E, hE, hAc, ?_, hCc, ?_⟩
  · intro j
    have h := E.sub_mem (hX 1 (matrix_col_mem_range (A + (1 : ℂ) • B) j)) (hAc j)
    have he : (A + (1 : ℂ) • B).col j - A.col j = B.col j := by
      funext i
      change A i j + 1 * B i j - A i j = B i j
      ring
    exact he ▸ h
  · intro j
    have h := E.sub_mem (hY 1 (matrix_col_mem_range (C + (1 : ℂ) • D) j)) (hCc j)
    have he : (C + (1 : ℂ) • D).col j - C.col j = D.col j := by
      funext i
      change C i j + 1 * D i j - C i j = D i j
      ring
    exact he ▸ h

/-- The literal conjugated minors, away from an explicit countable
exceptional set, suffice in the two-anchor branch. -/
theorem jointAffinePencil_common_plane_off_countable
    (A B : Matrix (Fin 3) κ ℂ) (C D : Matrix (Fin 3) ν ℂ)
    (s : Set ℂ) (hs : s.Countable)
    (hp : ∀ z ∉ s, ∀ cols : Fin 3 → κ ⊕ ν,
      ((jointAffinePencil A B C D z (conj z)).submatrix id cols).det = 0)
    (z₀ w₀ : ℂ) (hA : (A + z₀ • B).rank = 2) (hC : (C + w₀ • D).rank = 2) :
    ∃ E : Submodule ℂ (Fin 3 → ℂ), Module.finrank ℂ E = 2 ∧
      (∀ j, A.col j ∈ E) ∧ (∀ j, B.col j ∈ E) ∧
      (∀ j, C.col j ∈ E) ∧ (∀ j, D.col j ∈ E) := by
  apply jointAffinePencil_common_plane_of_two_anchors A B C D _ z₀ w₀ hA hC
  intro z w
  exact rank_le_two_of_all_three_minors_zero _
    (jointAffinePencil_minors_separate_off_countable A B C D s hs hp z w)

end ThreeCopyQutritWerner
