module

public import ThreeCopyQutritWerner.BinaryCutClassification
public import ThreeCopyQutritWerner.BinaryPartitionHalfNorm

@[expose] public section


/-!
# Exact unit-vector normalization of the binary cut classification

The identity branches have a rank-one factor of squared norm one half.
The existing half-norm theorem absorbs its complete complex phase into a
unit vector, so every branch has the manuscript's literal normalization.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Complete normalized binary cut forms, with unit ket-bra vectors and no
remaining scale or phase premise on the identity branches. -/
theorem binaryCut_normalized_unit_vector_classification
    (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hr : C.rank = 2) (hN : frobSq C = 1) (hz : cutForm C = 0) :
    (∃ x y : Fin 2 → ℂ, vecNormSq x = 1 ∧ vecNormSq y = 1 ∧
      C = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ketBra x y)) ∨
    (∃ x y : Fin 2 → ℂ, vecNormSq x = 1 ∧ vecNormSq y = 1 ∧
      C = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra x y ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) ∨
    (∃ U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ, Uᴴ * U = 1 ∧ C = binaryB₂ U) := by
  have hI : frobSq (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
    norm_num [frobSq, Matrix.one_apply, Fin.sum_univ_two]
  rcases binaryCut_normalized_rank_two_classification C hr hN hz with ⟨u, v, he⟩ | hB
  · have hT : (ketBra u v).rank ≤ 1 := Matrix.rank_vecMulVec_le u (fun j => conj (v j))
    rcases he with he | he
    · have hn : frobSq (ketBra u v) = 1 / 2 := by
        rw [he, ← tensor₂_eq_kronecker, frobSq_tensor₂, hI] at hN
        linarith
      obtain ⟨x, y, hx, hy, hxy⟩ := binaryPartition_rank_one_half_norm _ hT hn
      refine Or.inl ⟨x, y, hx, hy, ?_⟩
      rw [he, hxy, Matrix.kronecker_smul]
    · have hn : frobSq (ketBra u v) = 1 / 2 := by
        rw [he, ← tensor₂_eq_kronecker, frobSq_tensor₂, hI] at hN
        linarith
      obtain ⟨x, y, hx, hy, hxy⟩ := binaryPartition_rank_one_half_norm _ hT hn
      refine Or.inr (Or.inl ⟨x, y, hx, hy, ?_⟩)
      rw [he, hxy, Matrix.smul_kronecker]
  · exact Or.inr (Or.inr hB)

end ThreeCopyQutritWerner
