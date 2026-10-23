module

public import ThreeCopyQutritWerner.BinaryCutClassification

@[expose] public section


/-!
# The remaining factor of an actual doubled identity has rank at most one

The remaining dimension is arbitrary. Two-by-two submatrices reduce to the
proved binary identity-factor bound, and their exact minors give a literal
rank-one factorization. This keeps unrestricted two-qutrit inactive rays.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Vanishing ordinary two-by-two minors gives rank at most one, including
the zero matrix and arbitrary rectangular finite dimensions. -/
theorem matrix_rank_le_one_of_two_minors_zero
    {m n : Type*} [Fintype m] [Fintype n] (T : Matrix m n ℂ)
    (h : ∀ i j k l, T i k * T j l = T i l * T j k) : T.rank ≤ 1 := by
  by_cases hzero : T = 0
  · simp [hzero]
  obtain ⟨i₀, j₀, hp⟩ : ∃ i j, T i j ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hzero (by ext i j; exact hn i j)
  have he : T = Matrix.vecMulVec (fun i => T i j₀) (fun j => T i₀ j / T i₀ j₀) := by
    ext i j
    change T i j = T i j₀ * (T i₀ j / T i₀ j₀)
    rw [← mul_div_assoc]
    exact (eq_div_iff hp).mpr (h i i₀ j j₀)
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

/-- The exact binary identity factor doubles every two-dimensional minor;
a global rank bound of two leaves an arbitrary remaining factor rank one. -/
theorem binary_identity_tensor_rank_le_one
    {n : Type*} [Fintype n] (T : Matrix n n ℂ)
    (h : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T).rank ≤ 2) : T.rank ≤ 1 := by
  apply matrix_rank_le_one_of_two_minors_zero
  intro i j k l
  let S : Matrix (Fin 2) (Fin 2) ℂ := T.submatrix ![i, j] ![k, l]
  have hs : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ S).rank ≤ 2 := by
    have he : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ S =
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T).submatrix
          (fun p : Fin 2 × Fin 2 => (p.1, ![i, j] p.2))
          (fun p : Fin 2 × Fin 2 => (p.1, ![k, l] p.2)) := rfl
    rw [he]
    exact (Matrix.rank_submatrix_le _ _ _).trans h
  have hr := binary_identity_factor_rank_le_one S (Or.inl hs)
  have hd : S.det = 0 := by
    by_contra hn
    have he := Matrix.rank_of_det_ne_zero hn
    simp only [Fintype.card_fin] at he
    omega
  have hm : T i k * T j l - T i l * T j k = 0 := by
    rw [Matrix.det_fin_two] at hd
    simpa only [S, Matrix.submatrix_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] using hd
  exact sub_eq_zero.mp hm

end ThreeCopyQutritWerner
