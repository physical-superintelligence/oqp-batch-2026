module

public import ThreeCopyQutritWerner.ThinSourceCoordinates

@[expose] public section


/-!
# Whole singular-family coordinates of the original cut sources

A common missing coordinate of both actual singular families transfers
through the proved transition/source range equality to every original source
slice. Both remaining physical registers are handled in their original order.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

namespace ThreeCopyQutritWerner

/-- A common annihilator at the third register bounds its actual local range. -/
theorem localRangeDim₃_two_ray_le_two_of_common_annihilator
    {L R : Type*} [Fintype L] [Fintype R]
    (u v : L × R × Fin 3 → ℂ) (z w : ℂ)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : Uᴴ * U = 1) (a : Fin 3)
    (hu : ∀ l j, ∑ i, U a i * u (l, j, i) = 0)
    (hv : ∀ l j, ∑ i, U a i * v (l, j, i) = 0) :
    localRangeDim₃ (z • ketBra u u + w • ketBra v v) ≤ 2 := by
  rw [localRangeDim₃_eq_coherentFlatten_rank]
  apply rank_le_two_of_unitary_zero_row _ U hU a
  intro p
  change (∑ i, U a i *
    (z * (u (p.1.1, p.1.2, i) * conj (u p.2)) +
      w * (v (p.1.1, p.1.2, i) * conj (v p.2)))) = 0
  calc
    _ = z * (∑ i, U a i * u (p.1.1, p.1.2, i)) * conj (u p.2) +
        w * (∑ i, U a i * v (p.1.1, p.1.2, i)) * conj (v p.2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ = 0 := by rw [hu, hv]; ring

/-- An actual whole-family first-factor annihilator transfers to both cut
sources, using their actual transition ranges. -/
theorem zeroReserve_singular_first_annihilator_sources
    {L : Type*} [Fintype L] [DecidableEq L]
    (u v : L × (Fin 3 × Fin 3) → ℂ)
    (hRu : LinearMap.range (ptraceL (ketBra u v)).mulVecLin =
      LinearMap.range (zeroReserveCutFlatten u).mulVecLin)
    (hRv : LinearMap.range ((ptraceL (ketBra u v))ᴴ).mulVecLin =
      LinearMap.range (zeroReserveCutFlatten v).mulVecLin)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3)
    (h : ∀ k : SingularPositiveIndex (ptraceL (ketBra u v)), ∀ c,
      (U * sharpReshape (singularLeft (ptraceL (ketBra u v)) k)) a c = 0 ∧
      (U * sharpReshape (singularRight (ptraceL (ketBra u v)) k)) a c = 0) :
    (∀ l j, ∑ i, U a i * u (l, i, j) = 0) ∧
    (∀ l j, ∑ i, U a i * v (l, i, j) = 0) := by
  let X := ptraceL (ketBra u v)
  let W := U ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)
  have hleft (k : SingularPositiveIndex X) (c : Fin 3) :
      (W *ᵥ singularLeft X k) (a, c) = 0 := by
    simpa [W, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, mul_ite,
      Matrix.mul_apply, sharpReshape] using (h k c).1
  have hright (k : SingularPositiveIndex X) (c : Fin 3) :
      (W *ᵥ singularRight X k) (a, c) = 0 := by
    simpa [W, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, mul_ite,
      Matrix.mul_apply, sharpReshape] using (h k c).2
  constructor
  · intro l j
    have hz := matrix_zero_row_of_range_eq X (zeroReserveCutFlatten u) W hRu
      (a, j) (fun q => singularLeft_transform_zero_row X W (a, j)
        (fun k => hleft k j) q) l
    simpa [W, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, zeroReserveCutFlatten, ite_mul, mul_ite] using hz
  · intro l j
    have hz := matrix_zero_row_of_range_eq Xᴴ (zeroReserveCutFlatten v) W hRv
      (a, j) (fun q => singularRight_transform_zero_row X W (a, j)
        (fun k => hright k j) q) l
    simpa [W, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, zeroReserveCutFlatten, ite_mul, mul_ite] using hz

/-- The second-factor version keeps the physical third register in place. -/
theorem zeroReserve_singular_second_annihilator_sources
    {L : Type*} [Fintype L] [DecidableEq L]
    (u v : L × (Fin 3 × Fin 3) → ℂ)
    (hRu : LinearMap.range (ptraceL (ketBra u v)).mulVecLin =
      LinearMap.range (zeroReserveCutFlatten u).mulVecLin)
    (hRv : LinearMap.range ((ptraceL (ketBra u v))ᴴ).mulVecLin =
      LinearMap.range (zeroReserveCutFlatten v).mulVecLin)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3)
    (h : ∀ k : SingularPositiveIndex (ptraceL (ketBra u v)), ∀ c,
      (U * (sharpReshape (singularLeft (ptraceL (ketBra u v)) k))ᵀ) a c = 0 ∧
      (U * (sharpReshape (singularRight (ptraceL (ketBra u v)) k))ᵀ) a c = 0) :
    (∀ l j, ∑ i, U a i * u (l, j, i) = 0) ∧
    (∀ l j, ∑ i, U a i * v (l, j, i) = 0) := by
  let X := ptraceL (ketBra u v)
  let W := (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ U
  have hleft (k : SingularPositiveIndex X) (c : Fin 3) :
      (W *ᵥ singularLeft X k) (c, a) = 0 := by
    simpa [W, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, mul_ite,
      Matrix.mul_apply, sharpReshape, Matrix.transpose_apply] using (h k c).1
  have hright (k : SingularPositiveIndex X) (c : Fin 3) :
      (W *ᵥ singularRight X k) (c, a) = 0 := by
    simpa [W, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, mul_ite,
      Matrix.mul_apply, sharpReshape, Matrix.transpose_apply] using (h k c).2
  constructor
  · intro l j
    have hz := matrix_zero_row_of_range_eq X (zeroReserveCutFlatten u) W hRu
      (j, a) (fun q => singularLeft_transform_zero_row X W (j, a)
        (fun k => hleft k j) q) l
    simpa [W, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, zeroReserveCutFlatten, ite_mul, mul_ite] using hz
  · intro l j
    have hz := matrix_zero_row_of_range_eq Xᴴ (zeroReserveCutFlatten v) W hRv
      (j, a) (fun q => singularRight_transform_zero_row X W (j, a)
        (fun k => hright k j) q) l
    simpa [W, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, zeroReserveCutFlatten, ite_mul, mul_ite] using hz

end ThreeCopyQutritWerner
