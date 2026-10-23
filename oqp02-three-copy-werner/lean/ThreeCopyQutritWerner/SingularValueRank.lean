module

public import ThreeCopyQutritWerner.SingularNuclearTrace

@[expose] public section


/-!
# Rank and Hilbert--Schmidt identities for the actual singular family

The positive dilation index set has exactly the rank of the original matrix.
This binds the spectral family to rank-two hypotheses without selecting or
discarding singular vectors by an additional assumption.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

def singularLeftFrame {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) :
    Matrix m (SingularPositiveIndex X) ℂ := fun i j => singularLeft X j i

def singularRightFrame {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) :
    Matrix n (SingularPositiveIndex X) ℂ := fun i j => singularRight X j i

theorem singularLeftFrame_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) :
    (singularLeftFrame X)ᴴ * singularLeftFrame X = 1 := by
  ext i j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, singularLeftFrame,
    Matrix.one_apply, braket] using singularLeft_braket X i j

theorem singularRightFrame_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) :
    (singularRightFrame X)ᴴ * singularRightFrame X = 1 := by
  ext i j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, singularRightFrame,
    Matrix.one_apply, braket] using singularRight_braket X i j

/-- The original rectangular matrix, with adjoint on the right singular frame. -/
theorem singularFrame_factorization {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) :
    X = singularLeftFrame X * Matrix.diagonal (fun j => (singularWeight X j : ℂ)) *
      (singularRightFrame X)ᴴ := by
  classical
  ext i j
  rw [singularFamily_reconstruct X i j]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    singularLeftFrame, singularRightFrame, mul_assoc, mul_left_comm, mul_comm]

/-- The same actual frames recover every positive singular weight by compression. -/
theorem singularFrame_compression {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) :
    (singularLeftFrame X)ᴴ * X * singularRightFrame X =
      Matrix.diagonal (fun j => (singularWeight X j : ℂ)) := by
  calc
    _ = (singularLeftFrame X)ᴴ *
        (singularLeftFrame X * Matrix.diagonal (fun j => (singularWeight X j : ℂ)) *
          (singularRightFrame X)ᴴ) * singularRightFrame X :=
      congrArg (fun Y : Matrix m n ℂ =>
        (singularLeftFrame X)ᴴ * Y * singularRightFrame X) (singularFrame_factorization X)
    _ = ((singularLeftFrame X)ᴴ * singularLeftFrame X) *
        Matrix.diagonal (fun j => (singularWeight X j : ℂ)) *
        ((singularRightFrame X)ᴴ * singularRightFrame X) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [singularLeftFrame_gram, singularRightFrame_gram,
      Matrix.one_mul, Matrix.mul_one]

/-- Every positive spectral weight is nonzero as a complex scalar. -/
theorem singularWeight_complex_ne_zero {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (j : SingularPositiveIndex X) :
    (singularWeight X j : ℂ) ≠ 0 := by
  exact_mod_cast (singularWeight_pos X j).ne'

/-- There are exactly rank(X) positive Hermitian-dilation eigenvalues, with
multiplicity given by the actual spectral basis indices. -/
theorem singularPositive_card_eq_rank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) :
    Fintype.card (SingularPositiveIndex X) = X.rank := by
  classical
  let D := Matrix.diagonal (fun j : SingularPositiveIndex X => (singularWeight X j : ℂ))
  have hD : D.rank = Fintype.card (SingularPositiveIndex X) := by
    rw [Matrix.rank_diagonal]
    have hn (j : SingularPositiveIndex X) : singularWeight X j ≠ 0 :=
      (singularWeight_pos X j).ne'
    simp [hn]
  apply Nat.le_antisymm
  · rw [← hD]
    change (Matrix.diagonal (fun j => (singularWeight X j : ℂ))).rank ≤ X.rank
    rw [← singularFrame_compression X]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · conv_lhs => rw [singularFrame_factorization X]
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _))

/-- Adjoint does not change the literal Frobenius square. -/
theorem singular_frobSq_conjTranspose {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) : frobSq Xᴴ = frobSq X := by
  simp only [frobSq, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

/-- The squared actual singular weights sum to the original Frobenius square. -/
theorem singularWeight_sum_sq {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) :
    frobSq X = ∑ j : SingularPositiveIndex X, singularWeight X j ^ 2 := by
  classical
  calc
    frobSq X = frobSq (singularLeftFrame X *
        Matrix.diagonal (fun j => (singularWeight X j : ℂ)) *
          (singularRightFrame X)ᴴ) :=
      congrArg frobSq (singularFrame_factorization X)
    _ = frobSq (Matrix.diagonal (fun j : SingularPositiveIndex X =>
        (singularWeight X j : ℂ))) := by
      rw [Matrix.mul_assoc,
        nuclearTrace_frobSq_isometry_mul _ _ (singularLeftFrame_gram X),
        ← singular_frobSq_conjTranspose,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        nuclearTrace_frobSq_isometry_mul _ _ (singularRightFrame_gram X),
        singular_frobSq_conjTranspose]
    _ = _ := by
      simp [frobSq, Matrix.diagonal_apply, apply_ite, Complex.normSq_ofReal, pow_two]

end ThreeCopyQutritWerner
