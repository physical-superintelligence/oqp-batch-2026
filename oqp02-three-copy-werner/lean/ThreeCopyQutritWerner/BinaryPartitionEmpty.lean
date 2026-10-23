module

public import ThreeCopyQutritWerner.BinaryPartitionNonzero
public import ThreeCopyQutritWerner.SkewNormalizedFrame
public import ThreeCopyQutritWerner.ZeroRelations

@[expose] public section


/-!
# The empty first partition gives the literal normalized B₃ family

The factors on the empty site set are scalars, so the full spin transform
is skew. The existing normalized skew-frame theorem absorbs its entire
complex phase and gives the manuscript's exact B₃ normalization.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem binaryPartitionMatrix_empty_transpose
    (p q : ((∅ : Finset σ) → Fin 2) → ℂ)
    (r s : (↥((∅ : Finset σ)ᶜ) → Fin 2) → ℂ) :
    (binaryPartitionMatrix ∅ p q r s)ᵀ = -binaryPartitionMatrix ∅ p q r s := by
  ext a b
  have he : (fun i : (∅ : Finset σ) => a i) =
      (fun i : (∅ : Finset σ) => b i) := by
    funext i
    exact False.elim (Finset.notMem_empty (i : σ) i.property)
  simp only [Matrix.transpose_apply, Matrix.neg_apply, binaryPartitionMatrix, he]
  ring

/-- The word equivalence preserves the literal skew-transpose identity. -/
theorem binaryThreeWordMatrix_skew_iff
    (K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    (binaryThreeWordMatrix K)ᵀ = -binaryThreeWordMatrix K ↔ Kᵀ = -K := by
  constructor
  · intro h
    ext a b
    have he := congrFun (congrFun h (binaryThreeWordEquiv.symm a))
      (binaryThreeWordEquiv.symm b)
    simpa [binaryThreeWordMatrix] using he
  · intro h
    ext a b
    have he := congrFun (congrFun h (binaryThreeWordEquiv a)) (binaryThreeWordEquiv b)
    simpa [binaryThreeWordMatrix] using he

/-- The actual normalized original matrix in the empty-partition branch is
exactly B₃(U), with an actual orthonormal two-column frame. -/
theorem binaryPartition_empty_normalized_binaryB₃
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hC : C.rank ≤ 2) (hz : endpointEnergy C = 0) (hN : frobSq C = 1)
    (p q : ((∅ : Finset (Fin 3)) → Fin 2) → ℂ)
    (r s : (↥((∅ : Finset (Fin 3))ᶜ) → Fin 2) → ℂ)
    (he : binaryThreeWordMatrix (C * epsJ₃ᵀ) = binaryPartitionMatrix ∅ p q r s) :
    ∃ U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ,
      Uᴴ * U = 1 ∧ C = binaryB₃ U := by
  have hne : C ≠ 0 := by
    intro h
    simp [h, frobSq] at hN
  have hr := rank_eq_two_of_endpointEnergy_eq_zero C hC hz hne
  have hword : (binaryThreeWordMatrix (C * epsJ₃ᵀ))ᵀ =
      -binaryThreeWordMatrix (C * epsJ₃ᵀ) := by
    rw [he]
    exact binaryPartitionMatrix_empty_transpose p q r s
  have hskew := (binaryThreeWordMatrix_skew_iff (C * epsJ₃ᵀ)).mp hword
  rw [epsJ₃_transpose_eq_neg, Matrix.mul_neg, Matrix.transpose_neg, neg_neg] at hskew
  apply exists_binaryB₃_of_skew_spin C hr hN
  have hn := congrArg Neg.neg hskew
  simpa only [neg_neg] using hn

end ThreeCopyQutritWerner
