module

public import ThreeCopyQutritWerner.SharpDoubleAntisymmetric
public import ThreeCopyQutritWerner.BinaryZeros
public import ThreeCopyQutritWerner.Identities

@[expose] public section


/-!
# Actual local unitary congruence and the replica projection

Congruence uses ordinary transpose, as required for replica coefficient
matrices. Local coordinate changes commute with both replica swaps and their
double-antisymmetric projection. Actual unitaries preserve rank, Frobenius
square and the original complex Hilbert--Schmidt pairing.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Kronecker

namespace ThreeCopyQutritWerner

section Unitary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Transpose is a right unitary when the original matrix is an isometry. -/
theorem unitaryCongruence_transpose_right (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    Uᵀ * (Uᵀ)ᴴ = 1 := by
  simpa only [Matrix.transpose_mul, Matrix.transpose_one,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]
    using congrArg Matrix.transpose hU

/-- The literal two-sided inverse of the congruence transformation. -/
theorem unitaryCongruence_recover (U X : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    Uᴴ * (U * X * Uᵀ) * (Uᴴ)ᵀ = X := by
  have ht : Uᵀ * (Uᴴ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hU, Matrix.transpose_one]
  calc
    Uᴴ * (U * X * Uᵀ) * (Uᴴ)ᵀ = (Uᴴ * U) * X * (Uᵀ * (Uᴴ)ᵀ) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [hU, ht, Matrix.one_mul, Matrix.mul_one]

/-- Actual matrix rank is unchanged by unitary congruence. -/
theorem unitaryCongruence_rank (U X : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    (U * X * Uᵀ).rank = X.rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · calc
      X.rank = (Uᴴ * (U * X * Uᵀ) * (Uᴴ)ᵀ).rank :=
        congrArg Matrix.rank (unitaryCongruence_recover U X hU).symm
      _ ≤ (U * X * Uᵀ).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Actual Frobenius square is unchanged, including the zero matrix. -/
theorem unitaryCongruence_frobSq (U X : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    frobSq (U * X * Uᵀ) = frobSq X := by
  rw [frobSq_mul_unitary _ _ (unitaryCongruence_transpose_right U hU),
    frobSq_isometry_mul U hU]

/-- The complex pairing, including its phase, is unchanged. -/
theorem unitaryCongruence_hsInner (U X Y : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    hsInner (U * X * Uᵀ) (U * Y * Uᵀ) = hsInner X Y := by
  rw [hsInner_eq_trace, hsInner_eq_trace]
  have ht := unitaryCongruence_transpose_right U hU
  calc
    ((U * X * Uᵀ)ᴴ * (U * Y * Uᵀ)).trace =
        ((Uᵀ)ᴴ * (Xᴴ * (Uᴴ * U) * Y * Uᵀ)).trace := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((Uᵀ)ᴴ * (Xᴴ * Y * Uᵀ)).trace := by rw [hU, Matrix.mul_one]
    _ = (Xᴴ * Y * Uᵀ * (Uᵀ)ᴴ).trace := Matrix.trace_mul_comm _ _
    _ = (Xᴴ * Y).trace := by rw [Matrix.mul_assoc (Xᴴ * Y), ht, Matrix.mul_one]

end Unitary

section Local

variable {L R : Type*} [Fintype L] [Fintype R]

private theorem sharpLocalCongruence_entry
    (U : Matrix L L ℂ) (V : Matrix R R ℂ) (X : Matrix (L × R) (L × R) ℂ)
    (i j : L × R) :
    ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᵀ) i j =
      ∑ t : (L × R) × (L × R),
        (U i.1 t.1.1 * V i.2 t.1.2) * X t.1 t.2 *
          (U j.1 t.2.1 * V j.2 t.2.2) := by
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

/-- The first replica swap commutes with every actual local congruence. -/
theorem sharpSwapLeft_local_congruence
    (U : Matrix L L ℂ) (V : Matrix R R ℂ) (X : Matrix (L × R) (L × R) ℂ) :
    sharpSwapLeft ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᵀ) =
      (U ⊗ₖ V) * sharpSwapLeft X * (U ⊗ₖ V)ᵀ := by
  ext i j
  change ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᵀ) (j.1, i.2) (i.1, j.2) = _
  rw [sharpLocalCongruence_entry, sharpLocalCongruence_entry]
  apply Fintype.sum_equiv (swapLeft (L := L) (R := R))
  intro t
  simp only [swapLeft, Equiv.coe_fn_mk, sharpSwapLeft]
  ring

/-- The second replica swap commutes with every actual local congruence. -/
theorem sharpSwapRight_local_congruence
    (U : Matrix L L ℂ) (V : Matrix R R ℂ) (X : Matrix (L × R) (L × R) ℂ) :
    sharpSwapRight ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᵀ) =
      (U ⊗ₖ V) * sharpSwapRight X * (U ⊗ₖ V)ᵀ := by
  ext i j
  change ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᵀ) (i.1, j.2) (j.1, i.2) = _
  rw [sharpLocalCongruence_entry, sharpLocalCongruence_entry]
  apply Fintype.sum_equiv (swapRight (L := L) (R := R))
  intro t
  simp only [swapRight, Equiv.coe_fn_mk, sharpSwapRight]
  ring

private theorem sharpDoubleAnti_matrix_formula (X : Matrix (L × R) (L × R) ℂ) :
    sharpDoubleAnti X = (1 / 4 : ℂ) • (X - sharpSwapLeft X - sharpSwapRight X + Xᵀ) := by
  ext i j
  simp only [sharpDoubleAnti, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.sub_apply, Matrix.transpose_apply]
  ring

/-- The actual double-antisymmetrizer is equivariant on every matrix, not
only on a supplied encoder representation of its range. -/
theorem sharpDoubleAnti_local_congruence
    (U : Matrix L L ℂ) (V : Matrix R R ℂ) (X : Matrix (L × R) (L × R) ℂ) :
    sharpDoubleAnti ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᵀ) =
      (U ⊗ₖ V) * sharpDoubleAnti X * (U ⊗ₖ V)ᵀ := by
  rw [sharpDoubleAnti_matrix_formula, sharpDoubleAnti_matrix_formula,
    sharpSwapLeft_local_congruence, sharpSwapRight_local_congruence]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

variable [DecidableEq L] [DecidableEq R]

/-- The tensor product of the actual local isometries is itself an isometry. -/
theorem sharpLocalCongruence_unitary (U : Matrix L L ℂ) (V : Matrix R R ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    hU, hV, Matrix.one_kronecker_one]

/-- Sharp equality of the actual rank-two projection bound survives the
physical change to diagonal coefficient coordinates. -/
theorem sharpDoubleAnti_equality_local_congruence
    (U : Matrix L L ℂ) (V : Matrix R R ℂ) (X : Matrix (L × R) (L × R) ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    frobSq (sharpDoubleAnti ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᵀ)) =
        frobSq ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᵀ) / 2 ↔
      frobSq (sharpDoubleAnti X) = frobSq X / 2 := by
  rw [sharpDoubleAnti_local_congruence,
    unitaryCongruence_frobSq _ _ (sharpLocalCongruence_unitary U V hU hV),
    unitaryCongruence_frobSq _ _ (sharpLocalCongruence_unitary U V hU hV)]

end Local

end ThreeCopyQutritWerner
