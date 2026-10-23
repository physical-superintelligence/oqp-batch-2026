module

public import ThreeCopyQutritWerner.SingularValueRank
public import ThreeCopyQutritWerner.OrthonormalUnitaryExtension
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section


/-!
# Completing the actual singular families to square unitary matrices

Both positive singular families use the same embedded coordinate labels.
Their orthogonal complements are supplied by the existing finite-dimensional
isometry extension theorem, including rank zero.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- An actual orthonormal family occurs in prescribed distinct columns of a
square unitary. The other columns are constructed, not supplied as input. -/
theorem orthonormalFamily_exists_unitary_columns
    {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
    (e : k ↪ n) (u : k → n → ℂ)
    (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ ∀ j i, U i (e j) = u j i := by
  classical
  let v : k → n → ℂ := fun j i => if i = e j then 1 else 0
  have hv : ∀ i j, braket (v i) (v j) = if i = j then 1 else 0 := by
    intro i j
    unfold braket
    rw [Finset.sum_eq_single (e i)]
    · simp [v, e.injective.eq_iff]
    · intro x _ hx
      simp [v, hx]
    · simp
  obtain ⟨U, hU, hmap⟩ := orthonormalFamilies_exists_unitary u v hu hv
  refine ⟨U, hU, ?_⟩
  intro j i
  simpa [Matrix.mulVec, dotProduct, v, mul_ite] using congrFun (hmap j) i

/-- The actual positive singular families of any square matrix admit two
full unitary completions with a common embedding of their spectral indices. -/
theorem singularFamily_exists_unitary_completion
    {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ e : SingularPositiveIndex X ↪ n,
      ∃ U V : Matrix n n ℂ, Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
        (∀ j i, U i (e j) = singularLeft X j i) ∧
        (∀ j i, V i (e j) = singularRight X j i) := by
  classical
  have hc : Fintype.card (SingularPositiveIndex X) ≤ Fintype.card n := by
    rw [singularPositive_card_eq_rank]
    exact Matrix.rank_le_card_width X
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  obtain ⟨U, hU, hleft⟩ := orthonormalFamily_exists_unitary_columns e
    (singularLeft X) (singularLeft_braket X)
  obtain ⟨V, hV, hright⟩ := orthonormalFamily_exists_unitary_columns e
    (singularRight X) (singularRight_braket X)
  exact ⟨e, U, V, hU, hV, hleft, hright⟩

/-- Every square matrix has a full unitary singular factorization with
nonnegative real diagonal values. The unused spectral coordinates get zero. -/
theorem singularFamily_exists_unitary_diagonal
    {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ U V : Matrix n n ℂ, ∃ d : n → ℝ,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧ (∀ i, 0 ≤ d i) ∧
        X = U * Matrix.diagonal (fun i => (d i : ℂ)) * Vᴴ := by
  classical
  obtain ⟨e, U, V, hU, hV, hleft, hright⟩ :=
    singularFamily_exists_unitary_completion X
  let d : n → ℝ := fun i => ∑ j : SingularPositiveIndex X,
    if e j = i then singularWeight X j else 0
  refine ⟨U, V, d, hU, hV, ?_, ?_⟩
  · intro i
    exact Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact (singularWeight_pos X j).le
      · exact le_rfl
  · ext i j
    change X i j = ∑ k, (U * Matrix.diagonal (fun a => (d a : ℂ))) i k *
      star (V j k)
    simp only [Matrix.mul_diagonal, d, Complex.ofReal_sum, apply_ite,
      Complex.ofReal_zero, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [singularFamily_reconstruct X i j]
    apply Finset.sum_congr rfl
    intro k _
    rw [hleft k i, hright k j]
    simp only [Complex.star_def]
    ring

/-- The corresponding actual left and right unitaries diagonalize the
original matrix, with nonnegative diagonal entries and no rank premise. -/
theorem singularFamily_exists_unitary_diagonalization
    {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ U V : Matrix n n ℂ, ∃ d : n → ℝ,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧ (∀ i, 0 ≤ d i) ∧
        Uᴴ * X * V = Matrix.diagonal (fun i => (d i : ℂ)) := by
  obtain ⟨U, V, d, hU, hV, hd, hX⟩ := singularFamily_exists_unitary_diagonal X
  refine ⟨U, V, d, hU, hV, hd, ?_⟩
  rw [hX]
  calc
    _ = (Uᴴ * U) * Matrix.diagonal (fun i => (d i : ℂ)) * (Vᴴ * V) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]

end ThreeCopyQutritWerner
