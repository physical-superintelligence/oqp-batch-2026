module

public import ThreeCopyQutritWerner.SharpLocalCongruence
public import ThreeCopyQutritWerner.SharpQutritDiagonalNormal
public import ThreeCopyQutritWerner.SharpQutritDiagonalOverlap
public import ThreeCopyQutritWerner.RankOne

@[expose] public section


/-!
# Actual sharp saturation forces exterior coefficient rank at most two

The physical local unitaries are constructed from the original coefficient
matrix. The improved diagonal overlap estimate and exact congruence
invariance exclude three nonzero exterior directions. No normal-form or
spectral equality premise is supplied to the final theorem.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Two independent actual unitary factors preserve the intervening rank. -/
theorem unitaryTwoSidedTranspose_rank {n : Type*} [Fintype n] [DecidableEq n]
    (U V X : Matrix n n ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (U * X * Vᵀ).rank = X.rank := by
  have ht : Vᵀ * (Vᴴ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hV, Matrix.transpose_one]
  have hrec : Uᴴ * (U * X * Vᵀ) * (Vᴴ)ᵀ = X := by
    calc
      _ = (Uᴴ * U) * X * (Vᵀ * (Vᴴ)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hU, ht, Matrix.one_mul, Matrix.mul_one]
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · calc
      X.rank = (Uᴴ * (U * X * Vᵀ) * (Vᴴ)ᵀ).rank := congrArg Matrix.rank hrec.symm
      _ ≤ (U * X * Vᵀ).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- A missing one of the three actual diagonal entries bounds the rank by two. -/
theorem qutrit_diagonal_rank_le_two_of_zero (d : Fin 3 → ℝ)
    (hd : d 0 = 0 ∨ d 1 = 0 ∨ d 2 = 0) :
    (Matrix.diagonal (fun i => (d i : ℂ))).rank ≤ 2 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, d k = 0 := by
    rcases hd with hd | hd | hd
    · exact ⟨0, hd⟩
    · exact ⟨1, hd⟩
    · exact ⟨2, hd⟩
  rw [Matrix.rank_diagonal, Fintype.card_subtype]
  have hsub : Finset.univ.filter (fun i : Fin 3 => (d i : ℂ) ≠ 0) ⊆
      Finset.univ.erase k := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    subst i
    exact hi (by simp [hk])
  simpa using Finset.card_le_card hsub

/-- Every nonzero actual sharp saturator has a constructed physical local
normal form with at least one exterior coefficient zero. -/
theorem sharpDoubleAnti_saturation_exists_degenerate_normal
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2)
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) (hpos : 0 < frobSq Y) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ d : Fin 3 → ℝ,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧ (∀ i, 0 ≤ d i) ∧
      sharpDoubleAnti ((U ⊗ₖ V) * Y * (U ⊗ₖ V)ᵀ) =
        sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) ∧
      (d 0 = 0 ∨ d 1 = 0 ∨ d 2 = 0) := by
  obtain ⟨U, V, d, hU, hV, hd, hnormal⟩ := sharpDoubleAnti_exists_qutrit_diagonal_normal Y
  have hW := sharpLocalCongruence_unitary U V hU hV
  have hQ : sharpDoubleAnti ((U ⊗ₖ V) * Y * (U ⊗ₖ V)ᵀ) =
      sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))) := by
    rw [sharpDoubleAnti_local_congruence]
    exact hnormal
  refine ⟨U, V, d, hU, hV, hd, hQ, ?_⟩
  apply sharpQutritDiagonal_saturation_forces_coefficient_zero d hd _
    (by rwa [unitaryCongruence_rank _ _ hW]) hQ
    ((sharpDoubleAnti_equality_local_congruence U V Y hU hV).mpr hs)
  rwa [unitaryCongruence_frobSq _ _ hW]

/-- The original coefficient matrix itself has rank at most two. This is a
necessary equality condition, not the remaining common-support classification. -/
theorem sharpDoubleAnti_saturation_coefficient_rank_le_two
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2)
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) :
    (sharpQutritAntiCoefficients (sharpDoubleAnti Y)).rank ≤ 2 := by
  by_cases hz : frobSq Y = 0
  · have hzero : Y = 0 := matrix_eq_zero_of_frobSq_eq_zero Y hz
    rw [hzero]
    have hq : sharpDoubleAnti (0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) = 0 := by
      ext i j
      simp [sharpDoubleAnti, sharpSwapLeft, sharpSwapRight]
    have hc : sharpQutritAntiCoefficients (0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) = 0 := rfl
    rw [hq, hc, Matrix.rank_zero]
    omega
  · have hpos : 0 < frobSq Y := lt_of_le_of_ne (frobSq_nonneg Y) (Ne.symm hz)
    obtain ⟨U, V, d, hU, hV, hd, hQ, hd0⟩ :=
      sharpDoubleAnti_saturation_exists_degenerate_normal Y hY hs hpos
    let K := sharpQutritAntiCoefficients (sharpDoubleAnti Y)
    have hrec : sharpQutritAntiEncode K = sharpDoubleAnti Y :=
      sharpQutritAntiEncode_projected_coefficients Y
    have he : sharpQutritExteriorAction U * K * (sharpQutritExteriorAction V)ᵀ =
        Matrix.diagonal (fun i => (d i : ℂ)) := by
      have hh := congrArg sharpQutritAntiCoefficients hQ
      rw [sharpDoubleAnti_local_congruence, ← hrec,
        sharpQutritAntiCoefficients_local_congruence,
        sharpQutritAntiCoefficients_encode] at hh
      exact hh
    have hr := qutrit_diagonal_rank_le_two_of_zero d hd0
    rw [← he, unitaryTwoSidedTranspose_rank _ _ _
      (sharpQutritExteriorAction_isometry U hU)
      (sharpQutritExteriorAction_isometry V hV)] at hr
    exact hr

end ThreeCopyQutritWerner
