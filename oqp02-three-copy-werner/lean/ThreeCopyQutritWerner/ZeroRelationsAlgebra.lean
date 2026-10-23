module

public import ThreeCopyQutritWerner.ZeroRelations

@[expose] public section


/-!
# Algebraic consequences of the zero relations

For a rank-two factorization, `H=0` is equivalent to
`C²=(Tr C)C/2`, and `H` factors through `C` on the left (eq. (23), Appendix C).
If the three local antisymmetric parts of the source bivector are nonzero, eq. (24) forces
`H` to be symmetric under every local swap. The separate implication from full local support
to those three nonvanishing conditions is not asserted here.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

section RankTwo

variable {n : Type*} [Fintype n]

/-- For a rank-two `C = X B`, the range inclusion `ran H ⊆ ran C` is witnessed by an
explicit right factor, rather than assumed as part of the model. -/
theorem hFeature_eq_mul_left_of_rank_two (X : Matrix n (Fin 2) ℂ)
    (B : Matrix (Fin 2) n ℂ) (hr : (X * B).rank = 2) :
    ∃ N : Matrix n n ℂ, hFeature (X * B) (bivecMat X) = (X * B) * N := by
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_eq_two B (rank_eq_two_of_mul X B hr).2
  refine ⟨R * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
    ((B * X - ((X * B).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * epsMat * Xᵀ)), ?_⟩
  rw [hFeature_eq_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc B R, hR, Matrix.one_mul]

/-- For independent source columns, vanishing of `H` forces the compression to be scalar. -/
theorem compress_eq_trace_smul_of_hFeature_eq_zero (X : Matrix n (Fin 2) ℂ)
    (B : Matrix (Fin 2) n ℂ) (L : Matrix (Fin 2) n ℂ) (hL : L * X = 1)
    (hz : hFeature (X * B) (bivecMat X) = 0) :
    B * X = ((X * B).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have ht : Xᵀ * Lᵀ = 1 := by
    rw [← Matrix.transpose_mul, hL, Matrix.transpose_one]
  have hc : L * hFeature (X * B) (bivecMat X) * Lᵀ =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        ((B * X - ((X * B).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * epsMat) := by
    rw [hFeature_formula, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc L X, hL, Matrix.one_mul, ht, Matrix.mul_one]
  have hc0 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      ((B * X - ((X * B).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * epsMat) = 0 := by
    rw [← hc, hz, Matrix.mul_zero, Matrix.zero_mul]
  have hs : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  have he := (smul_eq_zero.mp hc0).resolve_left hs
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M * epsMat) he
  rw [Matrix.mul_assoc, epsMat_mul_self, Matrix.mul_neg, Matrix.mul_one, Matrix.zero_mul] at hh
  exact sub_eq_zero.mp (neg_eq_zero.mp hh)

/-- Appendix C, the rank-zero case of `H`: `H=0` implies `C²=(Tr C)C/2`. -/
theorem mul_self_eq_trace_smul_of_hFeature_eq_zero (X : Matrix n (Fin 2) ℂ)
    (B : Matrix (Fin 2) n ℂ) (hr : (X * B).rank = 2)
    (hz : hFeature (X * B) (bivecMat X) = 0) :
    (X * B) * (X * B) = ((X * B).trace / 2) • (X * B) := by
  obtain ⟨L, hL⟩ := exists_left_inverse_of_rank_eq_two X (rank_eq_two_of_mul X B hr).1
  have hBX := compress_eq_trace_smul_of_hFeature_eq_zero X B L hL hz
  calc
    (X * B) * (X * B) = X * (B * X) * B := by simp only [Matrix.mul_assoc]
    _ = ((X * B).trace / 2) • (X * B) := by
      rw [hBX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- Both directions of the rank-zero case, with the scalar determined by the trace. -/
theorem hFeature_eq_zero_iff_mul_self_eq_trace_smul (X : Matrix n (Fin 2) ℂ)
    (B : Matrix (Fin 2) n ℂ) (hr : (X * B).rank = 2) :
    hFeature (X * B) (bivecMat X) = 0 ↔
      (X * B) * (X * B) = ((X * B).trace / 2) • (X * B) :=
  ⟨mul_self_eq_trace_smul_of_hFeature_eq_zero X B hr,
    hFeature_eq_zero_of_sq_of_rank X B hr ((X * B).trace / 2)⟩

end RankTwo

section Symmetry

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- A tensor with a nonzero right factor vanishes only if its left factor vanishes. -/
theorem eq_zero_of_pair_product_eq_zero
    {H P : Matrix (a × b × c) (a × b × c) ℂ}
    (h : ∀ r s r' s', H r s * P r' s' = 0) (hP : P ≠ 0) : H = 0 := by
  obtain ⟨r', s', hrs⟩ : ∃ r' s', P r' s' ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hP
    ext r s
    exact hn r s
  ext r s
  exact (mul_eq_zero.mp (h r s r' s')).resolve_right hrs

/-- Section 5.1 / Appendix C: the zero relations and nonvanishing of every `Aᵢp` force
symmetry of `H` under every local swap, without a support hypothesis. -/
theorem local_symmetry_of_zeroRelations
    (C P : Matrix (a × b × c) (a × b × c) ℂ) (hP : Pᵀ = -P)
    (h : ZeroRelations (hFeature C P) P)
    (h1 : siteAnti₁ P ≠ 0) (h2 : siteAnti₂ P ≠ 0) (h3 : siteAnti₃ P ≠ 0) :
    siteAnti₁ (hFeature C P) = 0 ∧ siteAnti₂ (hFeature C P) = 0 ∧
      siteAnti₃ (hFeature C P) = 0 := by
  have h23 := eq_zero_of_pair_product_eq_zero h.1 h1
  have h13 := eq_zero_of_pair_product_eq_zero h.2.1 h2
  have h12 := eq_zero_of_pair_product_eq_zero h.2.2 h3
  have hsym := hFeature_transpose_of_skew C P hP
  exact ⟨siteAnti₁_eq_zero_of_symm hsym h13 h12,
    siteAnti₂_eq_zero_of_symm hsym h12 h23, siteAnti₃_eq_zero_of_symm hsym h13 h23⟩

end Symmetry

end ThreeCopyQutritWerner

end
