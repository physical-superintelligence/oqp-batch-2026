module

public import ThreeCopyQutritWerner.SharpCoordinatePlane
public import ThreeCopyQutritWerner.SharpSingularRangeTransport

@[expose] public section


/-!
# Original range consequences of a rank-two physical anchor

The extra local unitary can be cancelled in a missing row. A rank-two reshape
then fills the shared column plane, and any annihilator of that anchor also
annihilates every vector whose reshape range it contains.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Invert the right local transpose without changing a vanishing row. -/
theorem sharpUnitaryTranspose_zero_row_cancel
    (A U V : Matrix (Fin 3) (Fin 3) ℂ) (hV : Vᴴ * V = 1) (a : Fin 3)
    (h : ∀ j, (U * A * Vᵀ) a j = 0) (j : Fin 3) : (U * A) a j = 0 := by
  have ht : Vᵀ * (Vᴴ)ᵀ = 1 := by rw [← Matrix.transpose_mul, hV, Matrix.transpose_one]
  have he : (U * A * Vᵀ) * (Vᴴ)ᵀ = U * A := by
    rw [Matrix.mul_assoc (U * A), ht, Matrix.mul_one]
  rw [← he, Matrix.mul_apply]
  simp only [h, zero_mul, Finset.sum_const_zero]

/-- A common physical missing coordinate forces the second reshape range
inside the rank-two anchor's original range. -/
theorem sharpPhysicalSupport_range_le_anchor
    (x y : Fin 3 × Fin 3 → ℂ) (hx : (sharpReshape x).rank = 2)
    (U V : Matrix (Fin 3) (Fin 3) ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (a : Fin 3) (hxs : ∀ j, ((U ⊗ₖ V) *ᵥ x) (a, j) = 0)
    (hys : ∀ j, ((U ⊗ₖ V) *ᵥ y) (a, j) = 0) :
    LinearMap.range (sharpReshape y).mulVecLin ≤
      LinearMap.range (sharpReshape x).mulVecLin := by
  apply sharpCoordinatePlane_unitary_range_le_anchor (sharpReshape x) (sharpReshape y)
    hx U hU a
  · intro j
    apply sharpUnitaryTranspose_zero_row_cancel _ U V hV a ?_ j
    intro k
    rw [← sharpReshape_kronecker_mulVec]
    exact hxs k
  · intro j
    apply sharpUnitaryTranspose_zero_row_cancel _ U V hV a ?_ j
    intro k
    rw [← sharpReshape_kronecker_mulVec]
    exact hys k

/-- Any original row annihilator of the anchor also annihilates a matrix
whose column range is contained in the anchor range. -/
theorem sharpSupport_zero_row_of_range_le
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix m p ℂ) (U : Matrix m m ℂ) (a : m)
    (ha : ∀ j, (U * A) a j = 0)
    (hle : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin)
    (j : p) : (U * B) a j = 0 := by
  have hb : (fun r => B r j) ∈ LinearMap.range B.mulVecLin := by
    refine ⟨Pi.single j 1, ?_⟩
    ext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  obtain ⟨z, hz⟩ := hle hb
  change A *ᵥ z = (fun r => B r j) at hz
  have he : (U * A) *ᵥ z = fun r => (U * B) r j := by
    rw [← Matrix.mulVec_mulVec, hz]
    rfl
  have hzero : ((U * A) *ᵥ z) a = 0 := by
    simp only [Matrix.mulVec, dotProduct, ha, zero_mul, Finset.sum_const_zero]
  have hentry := congrFun he a
  rw [hzero] at hentry
  exact hentry.symm

end ThreeCopyQutritWerner
