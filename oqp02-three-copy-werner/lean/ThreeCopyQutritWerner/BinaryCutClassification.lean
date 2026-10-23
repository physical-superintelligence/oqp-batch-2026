module

public import ThreeCopyQutritWerner.BinaryCutKernel

@[expose] public section


/-!
# Rank-two classification inside an actual binary two-site carrier

The nonzero-trace branch has an actual rank-one factor. Combined with the
trace-zero skew normal form, this classifies every normalized rank-two binary
cut zero. The qutrit thin-source-to-binary-carrier reduction remains separate.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- A doubled binary identity factor can have rank at most two only when the
remaining actual two-dimensional factor has rank at most one. -/
theorem binary_identity_factor_rank_le_one (T : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T).rank ≤ 2 ∨
      (T ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).rank ≤ 2) : T.rank ≤ 1 := by
  by_contra hn
  have hmax := Matrix.rank_le_card_height T
  have hr : T.rank = Fintype.card (Fin 2) := by
    simp only [Fintype.card_fin] at hmax ⊢
    omega
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hr)
  have hdet : T.det * R.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hR
  have ht : T.det ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hdet
    exact zero_ne_one hdet
  have hleft : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T).rank = 4 := by
    have hd : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T).det ≠ 0 := by
      simp [Matrix.det_kronecker, ht]
    simpa using Matrix.rank_of_det_ne_zero hd
  have hright : (T ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).rank = 4 := by
    have hd : (T ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := by
      simp [Matrix.det_kronecker, ht]
    simpa using Matrix.rank_of_det_ne_zero hd
  rcases h with h | h
  · rw [hleft] at h
    omega
  · rw [hright] at h
    omega

/-- The nonzero-trace binary cut branch has an actual ket-bra factor. -/
theorem binaryCut_nonzero_trace_rank_one_factor
    (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hr : C.rank ≤ 2) (hC : cutForm C = 0) (ht : C.trace ≠ 0) :
    ∃ u v : Fin 2 → ℂ,
      C = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ketBra u v ∨
      C = ketBra u v ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨T, hT⟩ := binaryCut_nonzero_trace_identity_factor C hr hC ht
  have htr : T.rank ≤ 1 := by
    apply binary_identity_factor_rank_le_one
    rcases hT with hT | hT
    · exact Or.inl (hT ▸ hr)
    · exact Or.inr (hT ▸ hr)
  obtain ⟨u, v, hu⟩ := exists_eq_ketBra_of_rank_le_one T htr
  exact ⟨u, v, hu ▸ hT⟩

/-- Complete normalized rank-two classification on the actual binary two-site
carrier. This is a component of Appendix C.3, not the qutrit reduction to it. -/
theorem binaryCut_normalized_rank_two_classification
    (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hr : C.rank = 2) (hN : frobSq C = 1) (hC : cutForm C = 0) :
    (∃ u v : Fin 2 → ℂ,
      C = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ketBra u v ∨
      C = ketBra u v ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∨
    (∃ U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ, Uᴴ * U = 1 ∧ C = binaryB₂ U) := by
  by_cases ht : C.trace = 0
  · exact Or.inr (binaryCut_trace_zero_normal_form C hr hN hC ht)
  · exact Or.inl (binaryCut_nonzero_trace_rank_one_factor C hr.le hC ht)

end ThreeCopyQutritWerner
