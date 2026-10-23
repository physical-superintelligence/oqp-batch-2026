module

public import ThreeCopyQutritWerner.TwoCutCommonCarrier
public import ThreeCopyQutritWerner.TwoCutNonzeroRank
public import ThreeCopyQutritWerner.TwoCutBinaryNormalization

@[expose] public section


/-!
# Complete normalized qutrit two-site cut-zero classification

The original rank bound, zero cut form and unit Frobenius norm construct a
common binary carrier. Its data are inherited from the original matrix, then
the existing binary classification gives both normalized projection/ket-bra
placements or the embedded B₂ family. No carrier, plane alignment, endpoint
inequality or classification is supplied as a hypothesis.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- The compressed original zero has exactly the normalized rank-two data
required by the binary classification. -/
theorem qutritCut_normalized_exists_binary_carrier
    (C : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hC : C.rank ≤ 2) (hz : cutForm C = 0) (hN : frobSq C = 1) :
    ∃ J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ,
      ∃ K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      J₁ᴴ * J₁ = 1 ∧ J₂ᴴ * J₂ = 1 ∧
        C = (J₁ ⊗ₖ J₂) * K * (J₁ ⊗ₖ J₂)ᴴ ∧
        K.rank = 2 ∧ frobSq K = 1 ∧ cutForm K = 0 := by
  have hne : C ≠ 0 := by
    intro he
    simp [he, frobSq] at hN
  have hr := rank_two_of_nonzero_cutForm_zero C hC hz hne
  obtain ⟨J₁, J₂, K, hJ₁, hJ₂, he⟩ := cutForm_zero_exists_binary_carrier C hC hz
  have hd := twoCut_local_conj_data J₁ J₂ hJ₁ hJ₂ K
  refine ⟨J₁, J₂, K, hJ₁, hJ₂, he, ?_, ?_, ?_⟩
  · exact hd.1.symm.trans ((congrArg Matrix.rank he).symm.trans hr)
  · exact hd.2.1.symm.trans ((congrArg frobSq he).symm.trans hN)
  · exact hd.2.2.symm.trans ((congrArg cutForm he).symm.trans hz)

/-- Every actual normalized qutrit two-site cut zero of rank at most two is
one of the two exact projection/ket-bra placements or an actual embedded B₂.
All local vectors and frames are normalized and all complex phases retained. -/
theorem qutritCut_normalized_classification
    (C : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hC : C.rank ≤ 2) (hz : cutForm C = 0) (hN : frobSq C = 1) :
    (∃ (J : Matrix (Fin 3) (Fin 2) ℂ) (x y : Fin 3 → ℂ),
      Jᴴ * J = 1 ∧ vecNormSq x = 1 ∧ vecNormSq y = 1 ∧
      C = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ((J * Jᴴ) ⊗ₖ ketBra x y)) ∨
    (∃ (J : Matrix (Fin 3) (Fin 2) ℂ) (x y : Fin 3 → ℂ),
      Jᴴ * J = 1 ∧ vecNormSq x = 1 ∧ vecNormSq y = 1 ∧
      C = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra x y ⊗ₖ (J * Jᴴ))) ∨
    (∃ (J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ)
      (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ),
      J₁ᴴ * J₁ = 1 ∧ J₂ᴴ * J₂ = 1 ∧ Uᴴ * U = 1 ∧
      C = (J₁ ⊗ₖ J₂) * binaryB₂ U * (J₁ ⊗ₖ J₂)ᴴ) := by
  obtain ⟨J₁, J₂, K, hJ₁, hJ₂, he, hr, hn, hk⟩ :=
    qutritCut_normalized_exists_binary_carrier C hC hz hN
  rcases binaryCut_normalized_unit_vector_classification K hr hn hk with
    ⟨x, y, hx, hy, hK⟩ | ⟨x, y, hx, hy, hK⟩ | ⟨U, hU, hK⟩
  · refine Or.inl ⟨J₁, J₂ *ᵥ x, J₂ *ᵥ y, hJ₁,
      (binaryPartition_isometry_vecNormSq J₂ hJ₂ x).trans hx,
      (binaryPartition_isometry_vecNormSq J₂ hJ₂ y).trans hy, ?_⟩
    rw [he, hK, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      binaryPartition_conj_ketBra]
  · refine Or.inr (Or.inl ⟨J₂, J₁ *ᵥ x, J₁ *ᵥ y, hJ₂,
      (binaryPartition_isometry_vecNormSq J₁ hJ₁ x).trans hx,
      (binaryPartition_isometry_vecNormSq J₁ hJ₁ y).trans hy, ?_⟩)
    rw [he, hK, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      binaryPartition_conj_ketBra]
  · refine Or.inr (Or.inr ⟨J₁, J₂, U, hJ₁, hJ₂, hU, ?_⟩)
    rw [he, hK]

end ThreeCopyQutritWerner
