module

public import ThreeCopyQutritWerner.TwoCutSourceFactor
public import ThreeCopyQutritWerner.TwoCutCoordinateCarrier
public import ThreeCopyQutritWerner.TwoCutSwap
public import ThreeCopyQutritWerner.MatrixRangeFactor

@[expose] public section


/-!
# One common coordinate carrier for cut zeros with a fixed source

The source anchor supplies the missing physical output coordinates. Every
other cut zero with that same source has the same input coordinates unless
the anchor itself has a one-dimensional local output factor. Consequently
all nondegenerate members use the same literal coordinate inclusions.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- A literal one-dimensional first-site output, with a nonzero pivot
coordinate retained so its scalar normalization is explicit. -/
def HasSingleFirstOutput {a d : Type*} (A : Matrix (a × d) (a × d) ℂ) : Prop :=
  ∃ (i₀ : a) (x : a → ℂ), x i₀ = 1 ∧
    ∀ i r q, A (i, r) q = x i * A (i₀, r) q

/-- Failure of a common input plane forces a one-site source factor on the
fixed anchor, not merely on the individual other matrix. -/
theorem twoCut_fixed_source_coordinates_or_anchor_factor
    (A B : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hB : B.rank ≤ 2) (hq : cutForm B = 0)
    (hR : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin)
    (a b : Fin 3) (hArow : ∀ i j q, i = a ∨ j = b → A (i, j) q = 0) :
    (∀ i j p, i = a ∨ j = b → B p (i, j) = 0) ∨
      HasSingleFirstOutput A ∨ HasSingleFirstOutput (twoCutSwap A) := by
  obtain ⟨R, hBR⟩ := matrix_exists_right_factor_of_range_le B A hR.symm.le
  have hBrow (i j : Fin 3) (q : Fin 3 × Fin 3) (hij : i = a ∨ j = b) : B (i, j) q = 0 := by
    rw [hBR, Matrix.mul_apply]
    simp only [hArow i j _ hij, zero_mul, Finset.sum_const_zero]
  rcases cutForm_zero_fixed_source_alignment_or_factor A B hB hq hR.le a
      (fun r q => hBrow a r q (Or.inl rfl)) with hfirst | hfactor
  · have hRs : LinearMap.range (twoCutSwap A).mulVecLin ≤
        LinearMap.range (twoCutSwap B).mulVecLin :=
      matrix_range_submatrix_equiv_le A B (Equiv.prodComm _ _) hR.le
    have hBs := twoCutSwap_data B
    have hsrow (r : Fin 3) (q : Fin 3 × Fin 3) : twoCutSwap B (b, r) q = 0 :=
      hBrow r b (q.2, q.1) (Or.inr rfl)
    rcases cutForm_zero_fixed_source_alignment_or_factor (twoCutSwap A) (twoCutSwap B)
        (hBs.1.trans_le hB) (hBs.2.2.trans hq) hRs b hsrow with hsecond | hfactor
    · left
      intro i j p hij
      rcases hij with hi | hj
      · subst i
        exact hfirst p j
      · subst j
        exact hsecond (p.2, p.1) i
    · exact Or.inr (Or.inr hfactor)
  · exact Or.inr (Or.inl hfactor)

/-- Outside the two explicit single-output source branches, every cut zero
on the same actual source has one fixed common input/output coordinate carrier. -/
theorem twoCut_fixed_source_common_coordinate_carrier
    (A B : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hB : B.rank ≤ 2) (hq : cutForm B = 0)
    (hR : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin)
    (a b : Fin 3) (hArow : ∀ i j q, i = a ∨ j = b → A (i, j) q = 0)
    (hfirst : ¬ HasSingleFirstOutput A) (hsecond : ¬ HasSingleFirstOutput (twoCutSwap A)) :
    ∃ K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      B = (qutritPlaneInclusion a ⊗ₖ qutritPlaneInclusion b) * K *
        (qutritPlaneInclusion a ⊗ₖ qutritPlaneInclusion b)ᴴ := by
  have hcol := twoCut_fixed_source_coordinates_or_anchor_factor A B hB hq hR a b hArow
  rcases hcol with hcol | hf | hs
  · obtain ⟨R, hBR⟩ := matrix_exists_right_factor_of_range_le B A hR.symm.le
    have hrow (i j : Fin 3) (q : Fin 3 × Fin 3) (hij : i = a ∨ j = b) : B (i, j) q = 0 := by
      rw [hBR, Matrix.mul_apply]
      simp only [hArow i j _ hij, zero_mul, Finset.sum_const_zero]
    let W := qutritPlaneInclusion a ⊗ₖ qutritPlaneInclusion b
    have hW : W * Wᴴ = sharpCoordinatePlaneProjection a ⊗ₖ sharpCoordinatePlaneProjection b := by
      dsimp only [W]
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        qutritPlaneInclusion_projection, qutritPlaneInclusion_projection]
    have hleft : W * Wᴴ * B = B := by
      rw [hW]
      exact twoCut_coordinate_projection_mul B a b hrow
    have hleftH : W * Wᴴ * Bᴴ = Bᴴ := by
      rw [hW]
      apply twoCut_coordinate_projection_mul Bᴴ a b
      intro i j q hij
      simp only [Matrix.conjTranspose_apply, hcol i j q hij, star_zero]
    have hright : B * (W * Wᴴ) = B := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc] using congrArg Matrix.conjTranspose hleftH
    refine ⟨Wᴴ * B * W, ?_⟩
    change B = W * (Wᴴ * B * W) * Wᴴ
    symm
    calc
      _ = (W * Wᴴ * B) * (W * Wᴴ) := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hleft, hright]
  · exact (hfirst hf).elim
  · exact (hsecond hs).elim

end ThreeCopyQutritWerner
