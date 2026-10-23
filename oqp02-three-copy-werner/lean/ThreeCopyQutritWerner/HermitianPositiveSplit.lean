module

public import ThreeCopyQutritWerner.TakagiPositivePart

@[expose] public section


/-!
# Positive spectral splitting under an actual unitary sign change

This complex Hermitian version is used for the singular-value family of an
arbitrary matrix. All spectral vectors come from the pinned spectral theorem.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

set_option maxHeartbeats 2000000

/-- A proved unitary conjugation carrying H to -H exchanges its positive and negative parts. -/
theorem hermitianPositiveSplit {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (U : Matrix.unitaryGroup n ℂ)
    (hU : Unitary.conjStarAlgAut ℂ _ U H = -H) :
    cfc (fun r : ℝ => max r 0) H -
      Unitary.conjStarAlgAut ℂ _ U (cfc (fun r : ℝ => max r 0) H) = H := by
  let φ := Unitary.conjStarAlgAut ℂ _ U
  have hφH : IsSelfAdjoint (φ H) := by rw [show φ H = -H from hU]; exact hH.isSelfAdjoint.neg
  have hc := StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) φ
    (fun r : ℝ => max r 0) H (by fun_prop) (by
      change Continuous (fun M : Matrix n n ℂ => (U : Matrix n n ℂ) * M * star (U : Matrix n n ℂ))
      fun_prop) hH.isSelfAdjoint hφH
  change cfc (fun r : ℝ => max r 0) H - φ (cfc (fun r : ℝ => max r 0) H) = H
  rw [hc, show φ H = -H from hU,
    ← cfc_comp_neg (fun r : ℝ => max r 0) H (by fun_prop) hH.isSelfAdjoint,
    ← cfc_sub (fun r : ℝ => max r 0) (fun r : ℝ => max (-r) 0) H]
  have hf : (fun r : ℝ => max r 0 - max (-r) 0) = id := by
    funext r
    by_cases hr : 0 ≤ r
    · simp [max_eq_left hr, max_eq_right (neg_nonpos.mpr hr)]
    · have hn : r ≤ 0 := le_of_not_ge hr
      simp [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
  rw [hf]
  exact cfc_id' ℝ H hH.isSelfAdjoint

/-- Literal complex coordinate expansion of the Hermitian spectral functional calculus. -/
theorem hermitian_cfc_entry {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (f : ℝ → ℝ) (i j : n) :
    cfc f H i j = ∑ k, (f (hH.eigenvalues k) : ℂ) *
      (hH.eigenvectorBasis k i) * conj (hH.eigenvectorBasis k j) := by
  rw [hH.cfc_eq]
  simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, Complex.star_def, mul_assoc, mul_left_comm, mul_comm]

/-- The Hermitian dilation of an arbitrary rectangular complex matrix. -/
def singularDilation {m n : Type*} (X : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  Matrix.fromBlocks 0 X Xᴴ 0

theorem singularDilation_isHermitian {m n : Type*} (X : Matrix m n ℂ) :
    (singularDilation X).IsHermitian := by
  change (singularDilation X)ᴴ = singularDilation X
  simp [singularDilation, Matrix.fromBlocks_conjTranspose]

/-- The actual grading matrix of the two summands. -/
def singularGrading {m n : Type*} [DecidableEq m] [DecidableEq n] :
    Matrix (m ⊕ n) (m ⊕ n) ℂ := Matrix.fromBlocks 1 0 0 (-1)

theorem singularGrading_mem_unitary {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] :
    singularGrading (m := m) (n := n) ∈ Matrix.unitaryGroup (m ⊕ n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change singularGrading * singularGradingᴴ = 1
  simp [singularGrading, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_one]

def singularGradingUnitary {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] : Matrix.unitaryGroup (m ⊕ n) ℂ :=
  ⟨singularGrading, singularGrading_mem_unitary⟩

/-- Grading conjugation negates precisely the two cross blocks. -/
theorem singularGrading_conj_blocks {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ) :
    Unitary.conjStarAlgAut ℂ _ (singularGradingUnitary (m := m) (n := n))
      (Matrix.fromBlocks A B C D) = Matrix.fromBlocks A (-B) (-C) D := by
  simp [Unitary.conjStarAlgAut_apply, singularGradingUnitary, singularGrading,
    Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

/-- The Hermitian dilation changes sign under its actual grading unitary. -/
theorem singularDilation_grading {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) :
    Unitary.conjStarAlgAut ℂ _ (singularGradingUnitary (m := m) (n := n))
      (singularDilation X) = -singularDilation X := by
  change Unitary.conjStarAlgAut ℂ _ singularGradingUnitary (Matrix.fromBlocks 0 X Xᴴ 0) = _
  rw [singularGrading_conj_blocks]
  simp [singularDilation, Matrix.fromBlocks_neg]

/-- The original rectangular matrix is twice the cross block of the positive dilation part. -/
theorem singularDilation_positive_cross {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (i : m) (j : n) :
    X i j = 2 * cfc (fun r : ℝ => max r 0) (singularDilation X) (Sum.inl i) (Sum.inr j) := by
  let P := cfc (fun r : ℝ => max r 0) (singularDilation X)
  have h := congrFun (congrFun (hermitianPositiveSplit (singularDilation X)
    (singularDilation_isHermitian X) singularGradingUnitary (singularDilation_grading X))
      (Sum.inl i)) (Sum.inr j)
  change (P - Unitary.conjStarAlgAut ℂ _ singularGradingUnitary P)
    (Sum.inl i) (Sum.inr j) = X i j at h
  nth_rw 2 [← Matrix.fromBlocks_toBlocks P] at h
  rw [singularGrading_conj_blocks] at h
  simp only [Matrix.sub_apply, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply,
    Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.submatrix_apply, sub_neg_eq_add] at h
  linear_combination -h

end ThreeCopyQutritWerner
