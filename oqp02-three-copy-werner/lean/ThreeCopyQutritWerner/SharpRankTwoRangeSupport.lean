module

public import ThreeCopyQutritWerner.SharpCrossSupport
public import ThreeCopyQutritWerner.SingularValueRank

@[expose] public section


/-!
# Physical support of both ranges of a rank-two sharp transition

At actual rank two, the two positive singular indices exhaust the original
singular family. The common support of that pair therefore supports the
entire original transition range and adjoint range, with the same unitaries.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

private theorem matrix_zero_row_right_mul
    {m n p : Type*} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) (i : m)
    (h : ∀ k, A i k = 0) (j : p) : (A * B) i j = 0 := by
  simp [Matrix.mul_apply, h]

/-- An annihilator of every actual left singular vector annihilates the
corresponding row of the original transformed matrix. -/
theorem singularLeft_transform_zero_row
    {m n p : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (X : Matrix m n ℂ) (W : Matrix p m ℂ) (i : p)
    (h : ∀ k : SingularPositiveIndex X, (W *ᵥ singularLeft X k) i = 0)
    (j : n) : (W * X) i j = 0 := by
  classical
  have hrow : ∀ k, (W * singularLeftFrame X) i k = 0 := h
  have he : W * X = (W * singularLeftFrame X) *
      (Matrix.diagonal (fun k => (singularWeight X k : ℂ)) * (singularRightFrame X)ᴴ) := by
    conv_lhs => rw [singularFrame_factorization X]
    simp only [Matrix.mul_assoc]
  rw [he]
  exact matrix_zero_row_right_mul _ _ i hrow j

/-- Right singular annihilators act on the original adjoint, with its
original conjugation convention and no new singular decomposition. -/
theorem singularRight_transform_zero_row
    {m n p : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (X : Matrix m n ℂ) (W : Matrix p n ℂ) (i : p)
    (h : ∀ k : SingularPositiveIndex X, (W *ᵥ singularRight X k) i = 0)
    (j : m) : (W * Xᴴ) i j = 0 := by
  classical
  have hrow : ∀ k, (W * singularRightFrame X) i k = 0 := h
  have he : W * Xᴴ = (W * singularRightFrame X) *
      ((Matrix.diagonal (fun k => (singularWeight X k : ℂ)))ᴴ *
        (singularLeftFrame X)ᴴ) := by
    conv_lhs => rw [singularFrame_factorization X]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [he]
  exact matrix_zero_row_right_mul _ _ i hrow j

/-- Actual rank two and sharp partial-trace saturation give a single
two-by-two local support for both complete ranges. -/
theorem sharpPartialTrace_rank_two_exists_range_support
    (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hr : X.rank = 2)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      ∀ (i j : Fin 3) (p : Fin 3 × Fin 3), i = a ∨ j = a →
        ((U ⊗ₖ V) * X) (i, j) p = 0 ∧ ((U ⊗ₖ V) * Xᴴ) (i, j) p = 0 := by
  classical
  let e : Fin 2 ≃ SingularPositiveIndex X :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, singularPositive_card_eq_rank, hr])
  have he : e 0 ≠ e 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (e.injective h)
  obtain ⟨U, V, a, hU, hV, ha⟩ :=
    sharpPartialTrace_singular_pair_exists_thin_coordinates X hsat (e 0) (e 1) he
  refine ⟨U, V, a, hU, hV, ?_⟩
  intro i j p hij
  have hall : ∀ k : SingularPositiveIndex X,
      ((U ⊗ₖ V) *ᵥ singularLeft X k) (i, j) = 0 ∧
      ((U ⊗ₖ V) *ᵥ singularRight X k) (i, j) = 0 := by
    intro k
    obtain ⟨t, rfl⟩ := e.surjective k
    fin_cases t
    · exact ⟨(ha i j hij).1, (ha i j hij).2.2.1⟩
    · exact ⟨(ha i j hij).2.1, (ha i j hij).2.2.2⟩
  exact ⟨singularLeft_transform_zero_row X _ (i, j) (fun k => (hall k).1) p,
    singularRight_transform_zero_row X _ (i, j) (fun k => (hall k).2) p⟩

end ThreeCopyQutritWerner
