module

public import ThreeCopyQutritWerner.ZeroReserveRankTwoSourceSupport
public import ThreeCopyQutritWerner.CoherentPencilSupport

@[expose] public section


/-!
# Physical local ranks from constructed missing source coordinates

A missing row in unitary coordinates bounds the original flattening rank.
The second local unitary can be inverted without changing a missing first
coordinate. These facts connect the actual two-source support to the literal
localRangeDim definition of the manuscript.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

namespace ThreeCopyQutritWerner

/-- A zero physical row prevents a three-row matrix from being surjective. -/
theorem rank_le_two_of_zero_row {n : Type*} [Fintype n]
    (A : Matrix (Fin 3) n ℂ) (a : Fin 3) (h : ∀ j, A a j = 0) : A.rank ≤ 2 := by
  classical
  have hle := Matrix.rank_le_card_height A
  simp only [Fintype.card_fin] at hle
  by_contra hn
  have hr : A.rank = Fintype.card (Fin 3) := by simp only [Fintype.card_fin]; omega
  have hsurj := Matrix.mulVec_surjective_iff_rank_eq_card.mpr hr
  obtain ⟨v, hv⟩ := hsurj (Pi.single a 1)
  have ha := congrFun hv a
  simpa [Matrix.mulVec, dotProduct, h] using ha

/-- A constructed unitary missing coordinate bounds the original rank. -/
theorem rank_le_two_of_unitary_zero_row {n : Type*} [Fintype n]
    (A : Matrix (Fin 3) n ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : Uᴴ * U = 1) (a : Fin 3) (h : ∀ j, (U * A) a j = 0) : A.rank ≤ 2 := by
  have hz := rank_le_two_of_zero_row (U * A) a h
  calc
    A.rank = (Uᴴ * (U * A)).rank := by
      rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    _ ≤ (U * A).rank := Matrix.rank_mul_le_right _ _
    _ ≤ 2 := hz

/-- Removing the second unitary preserves a missing first coordinate in
the original tensor source. -/
theorem tensor_source_zero_row_cancel_right {n : Type*} [Fintype n]
    (F : Matrix (Fin 3 × Fin 3) n ℂ)
    (U V : Matrix (Fin 3) (Fin 3) ℂ) (hV : Vᴴ * V = 1)
    (a : Fin 3) (h : ∀ j p, ((U ⊗ₖ V) * F) (a, j) p = 0)
    (j : Fin 3) (p : n) :
    ((U ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) * F) (a, j) p = 0 := by
  have hc : ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ Vᴴ) * (U ⊗ₖ V) =
      U ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hV]
  rw [← hc, Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type]
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, mul_ite, h]

/-- The physical missing source coordinate gives the literal local
annihilator of every original source slice. -/
theorem zeroReserve_source_coordinate_annihilator
    {L : Type*} [Fintype L] (u : L × (Fin 3 × Fin 3) → ℂ)
    (U V : Matrix (Fin 3) (Fin 3) ℂ) (hV : Vᴴ * V = 1)
    (a : Fin 3)
    (h : ∀ j p, ((U ⊗ₖ V) * zeroReserveCutFlatten u) (a, j) p = 0)
    (l : L) (j : Fin 3) : ∑ i, U a i * u (l, i, j) = 0 := by
  have he := tensor_source_zero_row_cancel_right (zeroReserveCutFlatten u) U V hV a h j l
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, zeroReserveCutFlatten, ite_mul, mul_ite] using he

/-- A common actual source annihilator bounds the original local range of
any weighted two-ray operator, with the weights and conjugations unchanged. -/
theorem localRangeDim₂_two_ray_le_two_of_common_annihilator
    {L R : Type*} [Fintype L] [Fintype R]
    (u v : L × Fin 3 × R → ℂ) (z w : ℂ)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : Uᴴ * U = 1) (a : Fin 3)
    (hu : ∀ l j, ∑ i, U a i * u (l, i, j) = 0)
    (hv : ∀ l j, ∑ i, U a i * v (l, i, j) = 0) :
    localRangeDim₂ (z • ketBra u u + w • ketBra v v) ≤ 2 := by
  rw [localRangeDim₂_eq_coherentFlatten_rank]
  apply rank_le_two_of_unitary_zero_row _ U hU a
  intro p
  change (∑ i, U a i *
    (z * (u (p.1.1, i, p.1.2) * conj (u p.2)) +
      w * (v (p.1.1, i, p.1.2) * conj (v p.2)))) = 0
  calc
    _ = z * (∑ i, U a i * u (p.1.1, i, p.1.2)) * conj (u p.2) +
        w * (∑ i, U a i * v (p.1.1, i, p.1.2)) * conj (v p.2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ = 0 := by rw [hu, hv]; ring

end ThreeCopyQutritWerner
