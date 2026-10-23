module

public import ThreeCopyQutritWerner.BinaryPartitionEmpty
public import ThreeCopyQutritWerner.BinaryPartitionSingleton
public import ThreeCopyQutritWerner.BinaryPartitionComplement

@[expose] public section


/-!
# Three-family classification of actual normalized binary endpoint zeros

The polynomial grid and its site partition are derived from the original
matrix. All three cardinality branches now have their exact normalized
tensor forms, with the original site placement restored. The reduction of
an arbitrary thin qutrit zero to a binary carrier remains a separate task.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem binaryPartitionSiteTuple_undo (i : Fin 3)
    (C D : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (he : C.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) = D) :
    C = D.submatrix (binaryPartitionSiteTuple i).symm (binaryPartitionSiteTuple i).symm := by
  ext a b
  have h := congrFun (congrFun he ((binaryPartitionSiteTuple i).symm a))
    ((binaryPartitionSiteTuple i).symm b)
  simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using h

/-- Every original normalized binary endpoint zero of rank at most two belongs
to one of the manuscript's three families, with their exact normalizations.
No polynomial factors, tensor partition, skewness, or phase is a premise. -/
theorem binary_endpoint_normalized_three_family_classification
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hC : C.rank ≤ 2) (hz : endpointEnergy C = 0) (hN : frobSq C = 1) :
    (∃ i : Fin 3, ∃ x y : (Fin 2 × Fin 2) → ℂ,
      vecNormSq x = 1 ∧ vecNormSq y = 1 ∧
      C = (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ
        ketBra x y).submatrix (binaryPartitionSiteTuple i).symm (binaryPartitionSiteTuple i).symm) ∨
    (∃ i : Fin 3, ∃ x y : Fin 2 → ℂ,
      ∃ U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ,
      vecNormSq x = 1 ∧ vecNormSq y = 1 ∧ Uᴴ * U = 1 ∧
      C = (ketBra x y ⊗ₖ binaryB₂ U).submatrix
        (binaryPartitionSiteTuple i).symm (binaryPartitionSiteTuple i).symm) ∨
    (∃ U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ,
      Uᴴ * U = 1 ∧ C = binaryB₃ U) := by
  have hne : C ≠ 0 := by
    intro h
    simp [h, frobSq] at hN
  have hr := rank_eq_two_of_endpointEnergy_eq_zero C hC hz hne
  obtain ⟨I, p, q, r, s, hcard, hp, hq, hrr, hs, hskew, he⟩ :=
    binary_endpoint_zero_exists_proper_partition_tensor C hC hz hne
  rcases hcard with hcard | hcard | hcard
  · have hI : I = ∅ := Finset.card_eq_zero.mp hcard
    subst I
    exact Or.inr (Or.inr (binaryPartition_empty_normalized_binaryB₃ C hC hz hN p q r s he))
  · obtain ⟨i, hI⟩ := Finset.card_eq_one.mp hcard
    subst I
    obtain ⟨x, y, U, hx, hy, hU, hnormal⟩ :=
      binaryPartition_singleton_normalized_binaryB₂ C hr hN i p q r s he
    exact Or.inr (Or.inl ⟨i, x, y, U, hx, hy, hU,
      binaryPartitionSiteTuple_undo i C _ hnormal⟩)
  · have hcompl : (Iᶜ).card = 1 := by simp [Finset.card_compl, hcard]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcompl
    have hI : I = ({i} : Finset (Fin 3))ᶜ := by rw [← hi, compl_compl]
    subst I
    obtain ⟨x, y, hx, hy, hnormal⟩ :=
      binaryPartition_complement_normalized_identity C hN i p q r s he
    exact Or.inl ⟨i, x, y, hx, hy, binaryPartitionSiteTuple_undo i C _ hnormal⟩

end ThreeCopyQutritWerner
