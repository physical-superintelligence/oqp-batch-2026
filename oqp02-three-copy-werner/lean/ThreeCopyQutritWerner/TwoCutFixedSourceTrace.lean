module

public import ThreeCopyQutritWerner.TwoCutFixedSourceCoordinates
public import ThreeCopyQutritWerner.TwoCutCommonCarrier
public import ThreeCopyQutritWerner.BinaryCutClassification

@[expose] public section


/-!
# Trace on a nondegenerate fixed source

A nonzero trace of a rank-two cut zero forces a literal one-dimensional
local output factor. Range inclusion transports that factor to an anchor.
Thus both exceptional source branches are kept explicit when concluding
that every cut zero on a nondegenerate fixed source has trace zero.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- A ket-bra first factor has one actual local output direction, including
the zero vector and zero matrix cases. -/
theorem hasSingleFirstOutput_ketBra_kronecker
    {d : Type*} (u v : Fin 3 → ℂ) (P : Matrix d d ℂ) :
    HasSingleFirstOutput (ketBra u v ⊗ₖ P) := by
  classical
  by_cases hu : u = 0
  · refine ⟨0, fun i => if i = 0 then 1 else 0, by simp, ?_⟩
    intro i r q
    simp [hu, ketBra, Matrix.kroneckerMap_apply]
  · obtain ⟨i₀, hi₀⟩ : ∃ i₀, u i₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (funext h)
    refine ⟨i₀, fun i => u i / u i₀, div_self hi₀, ?_⟩
    intro i r q
    simp only [Matrix.kroneckerMap_apply, ketBra]
    field_simp [hi₀] <;> ring

/-- Being a single local output factor is a property of the actual range. -/
theorem hasSingleFirstOutput_of_range_le
    {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a] [DecidableEq d]
    (A B : Matrix (a × d) (a × d) ℂ)
    (hR : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin)
    (hB : HasSingleFirstOutput B) : HasSingleFirstOutput A := by
  obtain ⟨i₀, x, hx, hf⟩ := hB
  exact ⟨i₀, x, hx, firstSite_output_factor_of_range_le A B hR i₀ x hf⟩

/-- Nonzero trace leaves one of the two literal single-output branches.
The binary carrier and ket-bra factor are constructed from the original zero. -/
theorem cutForm_zero_nonzero_trace_single_output
    (C : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hr : C.rank ≤ 2) (hq : cutForm C = 0) (ht : C.trace ≠ 0) :
    HasSingleFirstOutput C ∨ HasSingleFirstOutput (twoCutSwap C) := by
  obtain ⟨J₁, J₂, K, hJ₁, hJ₂, he⟩ := cutForm_zero_exists_binary_carrier C hr hq
  have hd := twoCut_local_conj_data J₁ J₂ hJ₁ hJ₂ K
  have hKr : K.rank ≤ 2 := hd.1.symm.trans_le (he ▸ hr)
  have hKq : cutForm K = 0 := hd.2.2.symm.trans (he ▸ hq)
  have hKt : K.trace ≠ 0 := by
    intro h
    apply ht
    rw [he, trace_conj_isometry _ (kron_isometry J₁ J₂ hJ₁ hJ₂), h]
  obtain ⟨u, v, hK | hK⟩ := binaryCut_nonzero_trace_rank_one_factor K hKr hKq hKt
  · have hC : C = (J₁ * J₁ᴴ) ⊗ₖ ketBra (J₂ *ᵥ u) (J₂ *ᵥ v) := by
      rw [he, hK, Matrix.conjTranspose_kronecker,
        ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        Matrix.mul_one, binaryPartition_conj_ketBra]
    have hs : twoCutSwap C = ketBra (J₂ *ᵥ u) (J₂ *ᵥ v) ⊗ₖ (J₁ * J₁ᴴ) := by
      rw [hC]
      ext p q
      simp only [twoCutSwap, Matrix.submatrix_apply, Equiv.prodComm_apply,
        Matrix.kroneckerMap_apply, Prod.swap]
      ring
    right
    rw [hs]
    exact hasSingleFirstOutput_ketBra_kronecker _ _ _
  · have hC : C = ketBra (J₁ *ᵥ u) (J₁ *ᵥ v) ⊗ₖ (J₂ * J₂ᴴ) := by
      rw [he, hK, Matrix.conjTranspose_kronecker,
        ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        Matrix.mul_one, binaryPartition_conj_ketBra]
    left
    rw [hC]
    exact hasSingleFirstOutput_ketBra_kronecker _ _ _

/-- Every cut zero whose range contains a nondegenerate fixed source has
zero trace. Neither equality of ranges nor a supplied carrier is needed. -/
theorem cutForm_zero_fixed_source_trace_zero
    (A B : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hB : B.rank ≤ 2) (hq : cutForm B = 0)
    (hR : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin)
    (hfirst : ¬ HasSingleFirstOutput A) (hsecond : ¬ HasSingleFirstOutput (twoCutSwap A)) :
    B.trace = 0 := by
  by_contra ht
  rcases cutForm_zero_nonzero_trace_single_output B hB hq ht with hf | hs
  · exact hfirst (hasSingleFirstOutput_of_range_le A B hR hf)
  · exact hsecond (hasSingleFirstOutput_of_range_le (twoCutSwap A) (twoCutSwap B)
      (matrix_range_submatrix_equiv_le A B (Equiv.prodComm _ _) hR) hs)

end ThreeCopyQutritWerner
