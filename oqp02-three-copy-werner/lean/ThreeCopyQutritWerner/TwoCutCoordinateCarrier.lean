module

public import ThreeCopyQutritWerner.TwoCutTensorCarrier

@[expose] public section


/-!
# Literal binary compression after actual coordinate alignment

When the same missing local coordinates annihilate the original rows and
columns, the two explicit coordinate inclusions give an exact common binary
carrier. The compressed matrix is the actual W-adjoint C W.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The two local coordinate projections fix every matrix with the corresponding
actual missing output coordinates. -/
theorem twoCut_coordinate_projection_mul
    {n : Type*} [Fintype n] (C : Matrix (Fin 3 × Fin 3) n ℂ) (a b : Fin 3)
    (hrow : ∀ i j q, i = a ∨ j = b → C (i, j) q = 0) :
    (sharpCoordinatePlaneProjection a ⊗ₖ sharpCoordinatePlaneProjection b) * C = C := by
  rw [sharpCoordinatePlaneProjection, sharpCoordinatePlaneProjection,
    Matrix.diagonal_kronecker_diagonal]
  ext ⟨i, j⟩ q
  rw [Matrix.diagonal_mul]
  by_cases hi : i = a
  · rw [hrow i j q (Or.inl hi)]
    simp
  · by_cases hj : j = b
    · rw [hrow i j q (Or.inr hj)]
      simp
    · simp [hi, hj]

/-- Actual aligned row and column coordinates supply the literal common
binary carrier, including zero and lower-rank matrices. -/
theorem twoCut_aligned_coordinates_exists_binary_carrier
    (C : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (a b : Fin 3)
    (hrow : ∀ i j q, i = a ∨ j = b → C (i, j) q = 0)
    (hcol : ∀ i j p, i = a ∨ j = b → C p (i, j) = 0) :
    ∃ J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ,
      ∃ K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      J₁ᴴ * J₁ = 1 ∧ J₂ᴴ * J₂ = 1 ∧
        C = (J₁ ⊗ₖ J₂) * K * (J₁ ⊗ₖ J₂)ᴴ := by
  let W := qutritPlaneInclusion a ⊗ₖ qutritPlaneInclusion b
  have hW : W * Wᴴ =
      sharpCoordinatePlaneProjection a ⊗ₖ sharpCoordinatePlaneProjection b := by
    dsimp only [W]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      qutritPlaneInclusion_projection, qutritPlaneInclusion_projection]
  have hleft : W * Wᴴ * C = C := by
    rw [hW]
    exact twoCut_coordinate_projection_mul C a b hrow
  have hleftH : W * Wᴴ * Cᴴ = Cᴴ := by
    rw [hW]
    apply twoCut_coordinate_projection_mul Cᴴ a b
    intro i j q hij
    simp only [Matrix.conjTranspose_apply, hcol i j q hij, star_zero]
  have hright : C * (W * Wᴴ) = C := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using congrArg Matrix.conjTranspose hleftH
  refine ⟨qutritPlaneInclusion a, qutritPlaneInclusion b, Wᴴ * C * W,
    qutritPlaneInclusion_isometry a, qutritPlaneInclusion_isometry b, ?_⟩
  change C = W * (Wᴴ * C * W) * Wᴴ
  symm
  calc
    W * (Wᴴ * C * W) * Wᴴ = (W * Wᴴ * C) * (W * Wᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = C := by rw [hleft, hright]

end ThreeCopyQutritWerner
