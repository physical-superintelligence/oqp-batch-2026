module

public import ThreeCopyQutritWerner.CoherentPencilSupport
public import ThreeCopyQutritWerner.CoherentReservePencil

@[expose] public section


/-!
# Original Gram support and coherent source flattenings

An arbitrary rectangular complex matrix factors through its own positive Gram
operator. This includes all rank-deficient phases of a coherent pencil. The
physical local range dimensions of ZZ† are exactly the local flattening ranks
of Z; no invertibility assumption on its two columns is needed.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The actual positive source and its rectangular factor have the same range. -/
theorem coherentGram_range_eq {m n : Type*} [Fintype m] [Fintype n]
    (Z : Matrix m n ℂ) :
    LinearMap.range (Z * Zᴴ).mulVecLin = LinearMap.range Z.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro v ⟨w, rfl⟩
    refine ⟨Zᴴ *ᵥ w, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  · exact Matrix.rank_self_mul_conjTranspose Z

/-- Every rectangular source factors through its own actual positive Gram,
including zero and deficient rank cases. -/
theorem coherentGram_exists_factor {m n : Type*} [Fintype m] [Fintype n]
    (Z : Matrix m n ℂ) : ∃ R : Matrix m n ℂ, (Z * Zᴴ) * R = Z := by
  classical
  have hc (j : n) : ∃ v : m → ℂ, (Z * Zᴴ) *ᵥ v = fun i => Z i j := by
    have h : (fun i => Z i j) ∈ LinearMap.range Z.mulVecLin := by
      refine ⟨Pi.single j 1, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
      rfl
    rw [← coherentGram_range_eq Z] at h
    exact h
  choose v hv using hc
  refine ⟨fun i j => v j i, ?_⟩
  ext i j
  exact congrFun (hv j) i

variable {a b c n : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype n]

/-- The source Gram's actual first local support equals the original flattening rank. -/
theorem coherentGram_localRangeDim₁ (Z : Matrix (a × b × c) n ℂ) :
    localRangeDim₁ (Z * Zᴴ) = (coherentFlatten₁ Z).rank := by
  rw [localRangeDim₁_eq_coherentFlatten_rank]
  apply le_antisymm (coherentFlatten₁_mul_rank_le Z Zᴴ)
  obtain ⟨R, hR⟩ := coherentGram_exists_factor Z
  have h := coherentFlatten₁_mul_rank_le (Z * Zᴴ) R
  rw [hR] at h
  exact h

/-- The same exact equality at the second physical site. -/
theorem coherentGram_localRangeDim₂ (Z : Matrix (a × b × c) n ℂ) :
    localRangeDim₂ (Z * Zᴴ) = (coherentFlatten₂ Z).rank := by
  rw [localRangeDim₂_eq_coherentFlatten_rank]
  apply le_antisymm (coherentFlatten₂_mul_rank_le Z Zᴴ)
  obtain ⟨R, hR⟩ := coherentGram_exists_factor Z
  have h := coherentFlatten₂_mul_rank_le (Z * Zᴴ) R
  rw [hR] at h
  exact h

/-- The same exact equality at the third physical site. -/
theorem coherentGram_localRangeDim₃ (Z : Matrix (a × b × c) n ℂ) :
    localRangeDim₃ (Z * Zᴴ) = (coherentFlatten₃ Z).rank := by
  rw [localRangeDim₃_eq_coherentFlatten_rank]
  apply le_antisymm (coherentFlatten₃_mul_rank_le Z Zᴴ)
  obtain ⟨R, hR⟩ := coherentGram_exists_factor Z
  have h := coherentFlatten₃_mul_rank_le (Z * Zᴴ) R
  rw [hR] at h
  exact h

/-- Rank at most two forces every literal three-column determinant to vanish. -/
theorem all_three_minors_zero_of_rank_le_two {m : Type*} [Fintype m]
    (Z : Matrix (Fin 3) m ℂ) (hZ : Z.rank ≤ 2) (cols : Fin 3 → m) :
    (Z.submatrix id cols).det = 0 := by
  by_contra h
  have hr := Matrix.rank_of_det_ne_zero h
  have hl := (Matrix.rank_submatrix_le Z id cols).trans hZ
  rw [hr] at hl
  norm_num at hl

/-- Thinness of the actual positive source supplies the precise minor premise
used by the existing infinite-pencil support theorem. -/
theorem coherentQutritFlatten_minors_of_thin_gram
    (Z : Matrix QutritSites (Fin 2) ℂ) (hZ : HasThinLocalRange (Z * Zᴴ)) :
    ∃ i : Fin 3, ∀ cols : Fin 3 → ((Fin 3 × Fin 3) × Fin 2),
      ((coherentQutritFlatten Z i).submatrix id cols).det = 0 := by
  rcases hZ with h | h | h
  · refine ⟨0, ?_⟩
    rw [coherentGram_localRangeDim₁] at h
    exact all_three_minors_zero_of_rank_le_two (coherentFlatten₁ Z) h
  · refine ⟨1, ?_⟩
    rw [coherentGram_localRangeDim₂] at h
    exact all_three_minors_zero_of_rank_le_two (coherentFlatten₂ Z) h
  · refine ⟨2, ?_⟩
    rw [coherentGram_localRangeDim₃] at h
    exact all_three_minors_zero_of_rank_le_two (coherentFlatten₃ Z) h

end ThreeCopyQutritWerner
