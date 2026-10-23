module

public import ThreeCopyQutritWerner.TwoCutZeroEquality
public import ThreeCopyQutritWerner.SharpCrossSupport

@[expose] public section


/-!
# Polarized-null pairs under actual local coordinate changes

The cut defect uses the same unconjugated polarized minors as the replica
projection. Their null equation is preserved by arbitrary two-sided matrix
multiplication. A diagonal rank-two anchor then forces its partner to have
the identical missing row and column; no input/output alignment is asserted.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- The literal `biAnti` coordinates are the existing polarized minors. -/
theorem biAnti_eq_zero_iff_sharpPolarizedMinor {L R : Type*} (u v : L × R → ℂ) :
    biAnti u v = 0 ↔
      ∀ i j k l, sharpPolarizedMinor (sharpReshape u) (sharpReshape v) i j k l = 0 := by
  constructor
  · intro h i j k l
    have he := congrFun h ((i, k), (j, l))
    simp only [biAnti, Pi.zero_apply] at he
    unfold sharpPolarizedMinor sharpReshape
    linear_combination he
  · intro h
    funext ⟨⟨i, k⟩, ⟨j, l⟩⟩
    have he := h i j k l
    simp only [sharpPolarizedMinor, sharpReshape] at he
    change biAnti u v ((i, k), (j, l)) = 0
    unfold biAnti
    linear_combination he

/-- Null polarized minors are preserved by the same actual left and right
coordinate changes on both matrices. No invertibility assumption is needed. -/
theorem sharpPolarizedMinor_two_sided_null
    {L R : Type*} [Fintype L] [Fintype R]
    (U : Matrix L L ℂ) (V : Matrix R R ℂ) (A B : Matrix L R ℂ)
    (h : ∀ i j k l, sharpPolarizedMinor A B i j k l = 0) :
    ∀ i j k l, sharpPolarizedMinor (U * A * V) (U * B * V) i j k l = 0 := by
  let u : L × R → ℂ := fun p => A p.1 p.2
  let v : L × R → ℂ := fun p => B p.1 p.2
  have hu : sharpReshape u = A := rfl
  have hv : sharpReshape v = B := rfl
  have hn : sharpDoubleAnti (sharpTensorRay u v) = 0 :=
    (sharpDoubleAnti_tensor_null_iff u v).mpr h
  have ht : sharpDoubleAnti
      (sharpTensorRay ((U ⊗ₖ Vᵀ) *ᵥ u) ((U ⊗ₖ Vᵀ) *ᵥ v)) = 0 := by
    rw [← sharpTensorRay_congruence, sharpDoubleAnti_local_congruence,
      hn, Matrix.mul_zero, Matrix.zero_mul]
  have hp := (sharpDoubleAnti_tensor_null_iff _ _).mp ht
  simpa only [sharpReshape_kronecker_mulVec, Matrix.transpose_transpose, hu, hv] using hp

/-- With precisely one zero diagonal coordinate, null polarization forces
the partner's corresponding whole row and whole column to vanish. -/
theorem sharpPolarizedMinor_diagonal_missing_coordinate
    (d : Fin 3 → ℂ) (a : Fin 3) (ha : d a = 0)
    (hd : ∀ j, j ≠ a → d j ≠ 0) (B : Matrix (Fin 3) (Fin 3) ℂ)
    (h : ∀ i j k l, sharpPolarizedMinor (Matrix.diagonal d) B i j k l = 0) :
    ∀ i, B a i = 0 ∧ B i a = 0 := by
  intro i
  obtain ⟨j, hja, hji⟩ : ∃ j : Fin 3, j ≠ a ∧ j ≠ i := by
    fin_cases a <;> fin_cases i <;> decide
  have hr : d j * B a i = 0 := by
    simpa [sharpPolarizedMinor, Matrix.diagonal_apply, ha, hja, hji,
      Ne.symm hja, Ne.symm hji] using h j a j i
  have hc : d j * B i a = 0 := by
    by_cases hia : i = a
    · subst i
      simpa [sharpPolarizedMinor, Matrix.diagonal_apply, ha, hja,
        Ne.symm hja] using h j a j a
    · simpa [sharpPolarizedMinor, Matrix.diagonal_apply, ha, hja, hji, hia,
        Ne.symm hja, Ne.symm hji] using h j i j a
  exact ⟨(mul_eq_zero.mp hr).resolve_left (hd j hja),
    (mul_eq_zero.mp hc).resolve_left (hd j hja)⟩

end ThreeCopyQutritWerner
