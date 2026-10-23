module

public import ThreeCopyQutritWerner.SharpQutritSaturationNormal

@[expose] public section


/-!
# Uniqueness of a rank-two physical column plane

A rank-two qutrit matrix with a missing unitary row fills that entire
coordinate plane. Every other matrix with the same missing row therefore
has its column range inside the original anchor range.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Orthogonal coordinate projection omitting one literal qutrit index. -/
def sharpCoordinatePlaneProjection (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i => if i = a then 0 else 1)

theorem sharpCoordinatePlaneProjection_rank (a : Fin 3) :
    (sharpCoordinatePlaneProjection a).rank = 2 := by
  rw [sharpCoordinatePlaneProjection, Matrix.rank_diagonal]
  classical
  rw [Fintype.card_subtype]
  have he : Finset.univ.filter (fun i : Fin 3 => (if i = a then (0 : ℂ) else 1) ≠ 0) =
      Finset.univ.erase a := by
    ext i
    by_cases hi : i = a <;> simp [hi]
  rw [he]
  simp

/-- Missing rows are fixed by the literal coordinate-plane projection. -/
theorem sharpCoordinatePlaneProjection_mul {n : Type*} [Fintype n]
    (A : Matrix (Fin 3) n ℂ) (a : Fin 3) (ha : ∀ j, A a j = 0) :
    sharpCoordinatePlaneProjection a * A = A := by
  ext i j
  rw [sharpCoordinatePlaneProjection, Matrix.diagonal_mul]
  by_cases hi : i = a
  · subst i
    simp [ha]
  · simp [hi]

/-- A rank-two anchor fills its two-dimensional coordinate plane exactly. -/
theorem sharpCoordinatePlane_range_le_anchor
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix (Fin 3) m ℂ) (B : Matrix (Fin 3) n ℂ)
    (hA : A.rank = 2) (a : Fin 3)
    (ha : ∀ j, A a j = 0) (hb : ∀ j, B a j = 0) :
    LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin := by
  have hAP : LinearMap.range A.mulVecLin ≤
      LinearMap.range (sharpCoordinatePlaneProjection a).mulVecLin := by
    rintro w ⟨v, rfl⟩
    refine ⟨A *ᵥ v, ?_⟩
    change sharpCoordinatePlaneProjection a *ᵥ (A *ᵥ v) = A *ᵥ v
    rw [Matrix.mulVec_mulVec, sharpCoordinatePlaneProjection_mul A a ha]
  have hBP : LinearMap.range B.mulVecLin ≤
      LinearMap.range (sharpCoordinatePlaneProjection a).mulVecLin := by
    rintro w ⟨v, rfl⟩
    refine ⟨B *ᵥ v, ?_⟩
    change sharpCoordinatePlaneProjection a *ᵥ (B *ᵥ v) = B *ᵥ v
    rw [Matrix.mulVec_mulVec, sharpCoordinatePlaneProjection_mul B a hb]
  have he : LinearMap.range A.mulVecLin =
      LinearMap.range (sharpCoordinatePlaneProjection a).mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq hAP
    change A.rank = (sharpCoordinatePlaneProjection a).rank
    rw [hA, sharpCoordinatePlaneProjection_rank]
  rw [he]
  exact hBP

/-- The same range inclusion holds in the original coordinates after an
actual unitary change of rows. -/
theorem sharpCoordinatePlane_unitary_range_le_anchor
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix (Fin 3) m ℂ) (B : Matrix (Fin 3) n ℂ)
    (hA : A.rank = 2) (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : Uᴴ * U = 1)
    (a : Fin 3) (ha : ∀ j, (U * A) a j = 0) (hb : ∀ j, (U * B) a j = 0) :
    LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin := by
  have hr : (U * A).rank = 2 := by
    have hlow : A.rank ≤ (U * A).rank := by
      calc
        A.rank = (Uᴴ * (U * A)).rank := by
          rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
        _ ≤ (U * A).rank := Matrix.rank_mul_le_right _ _
    exact le_antisymm ((Matrix.rank_mul_le_right U A).trans hA.le)
      (hA.ge.trans hlow)
  have hle := sharpCoordinatePlane_range_le_anchor (U * A) (U * B) hr a ha hb
  rintro w ⟨v, rfl⟩
  obtain ⟨z, hz⟩ := hle (show (U * B) *ᵥ v ∈ LinearMap.range (U * B).mulVecLin from ⟨v, rfl⟩)
  refine ⟨z, ?_⟩
  have he := congrArg (fun x => Uᴴ *ᵥ x) hz
  change Uᴴ *ᵥ ((U * A) *ᵥ z) = Uᴴ *ᵥ ((U * B) *ᵥ v) at he
  change A *ᵥ z = B *ᵥ v
  simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hU, Matrix.one_mul] using he

end ThreeCopyQutritWerner
