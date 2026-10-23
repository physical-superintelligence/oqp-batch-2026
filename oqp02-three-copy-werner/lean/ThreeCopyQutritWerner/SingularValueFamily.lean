module

public import ThreeCopyQutritWerner.HermitianPositiveSplit
public import ThreeCopyQutritWerner.TwoCutRotate

@[expose] public section


/-!
# Actual singular vectors from the positive Hermitian dilation spectrum

For [0 X; X-adjoint 0], positive eigenvectors have equal left and right
norms. Their components, multiplied by sqrt(2), are two orthonormal families.
Their positive eigenvalues reconstruct the original rectangular X.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Sesquilinearity at a real right scalar, in the original conjugate-first pairing. -/
theorem singular_braket_real_right {n : Type*} [Fintype n]
    (u v : n → ℂ) (a : ℝ) : braket u ((a : ℂ) • v) = (a : ℂ) * braket u v := by
  simp [braket, Finset.mul_sum, mul_assoc, mul_left_comm]

/-- Applying the same real scale to both slots contributes its square. -/
theorem singular_braket_real_scale {n : Type*} [Fintype n]
    (u v : n → ℂ) (a : ℝ) :
    braket ((a : ℂ) • u) ((a : ℂ) • v) = (a : ℂ) ^ 2 * braket u v := by
  simp only [braket, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Distinct real Hermitian eigenvalues have orthogonal eigenvectors. -/
theorem singular_hermitian_eigen_orthogonal {n : Type*} [Fintype n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (u v : n → ℂ) (a b : ℝ)
    (hu : H *ᵥ u = (a : ℂ) • u) (hv : H *ᵥ v = (b : ℂ) • v) (hab : a ≠ b) :
    braket u v = 0 := by
  have h := hH.star_dotProduct_mulVec_comm v u
  change conj (braket v (H *ᵥ u)) = braket u (H *ᵥ v) at h
  rw [hu, hv, singular_braket_real_right, singular_braket_real_right,
    map_mul, Complex.conj_ofReal, conj_braket] at h
  have hz : ((a - b : ℝ) : ℂ) * braket u v = 0 := by
    push_cast
    linear_combination h
  have hn : ((a - b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hab
  exact (mul_eq_zero.mp hz).resolve_left hn

/-- Grading on literal vector coordinates. -/
def singularGradeVector {m n : Type*} (v : m ⊕ n → ℂ) : m ⊕ n → ℂ :=
  Sum.elim (fun i => v (Sum.inl i)) (fun j => -v (Sum.inr j))

/-- The Hermitian dilation anticommutes with grading on actual vectors. -/
theorem singularDilation_grade_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) (v : m ⊕ n → ℂ) :
    singularDilation X *ᵥ singularGradeVector v =
      -singularGradeVector (singularDilation X *ᵥ v) := by
  funext i
  cases i <;>
    simp [singularDilation, singularGradeVector, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Finset.sum_neg_distrib]

/-- Positive spectral indices of the actual Hermitian dilation. -/
abbrev SingularPositiveIndex {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) :=
  {j : m ⊕ n // 0 < (singularDilation_isHermitian X).eigenvalues j}

/-- Actual positive singular weights. -/
def singularWeight {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (j : SingularPositiveIndex X) : ℝ :=
  (singularDilation_isHermitian X).eigenvalues j.val

/-- Normalized left component of a positive Hermitian-dilation eigenvector. -/
def singularLeft {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (j : SingularPositiveIndex X) : m → ℂ :=
  fun i => (Real.sqrt 2 : ℂ) * (singularDilation_isHermitian X).eigenvectorBasis j.val (Sum.inl i)

/-- Normalized right component of that same actual eigenvector. -/
def singularRight {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (j : SingularPositiveIndex X) : n → ℂ :=
  fun i => (Real.sqrt 2 : ℂ) * (singularDilation_isHermitian X).eigenvectorBasis j.val (Sum.inr i)

theorem singularWeight_pos {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (j : SingularPositiveIndex X) :
    0 < singularWeight X j := j.property

/-- Positive eigenvectors are orthogonal to every graded positive eigenvector. -/
theorem singularPositive_graded_pair_zero {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (i j : SingularPositiveIndex X) :
    braket ((singularDilation_isHermitian X).eigenvectorBasis i.val)
      (singularGradeVector ((singularDilation_isHermitian X).eigenvectorBasis j.val)) = 0 := by
  have hj := singularDilation_grade_mulVec X
    ((singularDilation_isHermitian X).eigenvectorBasis j.val)
  rw [(singularDilation_isHermitian X).mulVec_eigenvectorBasis j.val] at hj
  have hgraded : singularDilation X *ᵥ
      singularGradeVector ((singularDilation_isHermitian X).eigenvectorBasis j.val) =
        ((-(singularWeight X j) : ℝ) : ℂ) •
          singularGradeVector ((singularDilation_isHermitian X).eigenvectorBasis j.val) := by
    rw [hj]
    funext k
    cases k <;>
      simp [singularGradeVector, singularWeight, Pi.smul_apply, smul_eq_mul,
        RCLike.real_smul_eq_coe_mul]
  exact singular_hermitian_eigen_orthogonal _ (singularDilation_isHermitian X) _ _
    (singularWeight X i) (-(singularWeight X j))
    ((singularDilation_isHermitian X).mulVec_eigenvectorBasis i.val) hgraded
    (by have hi := i.property; have hj := j.property; dsimp [singularWeight]; linarith)

/-- The unscaled left components have precisely half the original delta Gram. -/
theorem singularPositive_left_half_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (i j : SingularPositiveIndex X) :
    2 * braket
      (fun k => (singularDilation_isHermitian X).eigenvectorBasis i.val (Sum.inl k))
      (fun k => (singularDilation_isHermitian X).eigenvectorBasis j.val (Sum.inl k)) =
        if i = j then 1 else 0 := by
  have hfull : braket ((singularDilation_isHermitian X).eigenvectorBasis i.val)
      ((singularDilation_isHermitian X).eigenvectorBasis j.val) = if i = j then 1 else 0 := by
    have h := (singularDilation_isHermitian X).eigenvectorBasis.inner_eq_ite i.val j.val
    simpa [EuclideanSpace.inner_eq_star_dotProduct, braket, dotProduct,
      mul_comm, Complex.star_def, Subtype.ext_iff] using h
  have hgrade := singularPositive_graded_pair_zero X i j
  simp only [braket, Fintype.sum_sum_type, singularGradeVector, Sum.elim_inl,
    Sum.elim_inr, mul_neg, Finset.sum_neg_distrib] at hfull hgrade ⊢
  linear_combination hfull + hgrade

/-- The unscaled right components have the same half-delta Gram. -/
theorem singularPositive_right_half_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (i j : SingularPositiveIndex X) :
    2 * braket
      (fun k => (singularDilation_isHermitian X).eigenvectorBasis i.val (Sum.inr k))
      (fun k => (singularDilation_isHermitian X).eigenvectorBasis j.val (Sum.inr k)) =
        if i = j then 1 else 0 := by
  have hfull : braket ((singularDilation_isHermitian X).eigenvectorBasis i.val)
      ((singularDilation_isHermitian X).eigenvectorBasis j.val) = if i = j then 1 else 0 := by
    have h := (singularDilation_isHermitian X).eigenvectorBasis.inner_eq_ite i.val j.val
    simpa [EuclideanSpace.inner_eq_star_dotProduct, braket, dotProduct,
      mul_comm, Complex.star_def, Subtype.ext_iff] using h
  have hgrade := singularPositive_graded_pair_zero X i j
  simp only [braket, Fintype.sum_sum_type, singularGradeVector, Sum.elim_inl,
    Sum.elim_inr, mul_neg, Finset.sum_neg_distrib] at hfull hgrade ⊢
  linear_combination hfull - hgrade

/-- The normalized actual left singular vectors are orthonormal. -/
theorem singularLeft_braket {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (i j : SingularPositiveIndex X) :
    braket (singularLeft X i) (singularLeft X j) = if i = j then 1 else 0 := by
  change braket ((Real.sqrt 2 : ℂ) • (fun k =>
      (singularDilation_isHermitian X).eigenvectorBasis i.val (Sum.inl k)))
    ((Real.sqrt 2 : ℂ) • (fun k =>
      (singularDilation_isHermitian X).eigenvectorBasis j.val (Sum.inl k))) = _
  rw [singular_braket_real_scale]
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hs]
  exact singularPositive_left_half_gram X i j

/-- The normalized actual right singular vectors are independently orthonormal. -/
theorem singularRight_braket {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (i j : SingularPositiveIndex X) :
    braket (singularRight X i) (singularRight X j) = if i = j then 1 else 0 := by
  change braket ((Real.sqrt 2 : ℂ) • (fun k =>
      (singularDilation_isHermitian X).eigenvectorBasis i.val (Sum.inr k)))
    ((Real.sqrt 2 : ℂ) • (fun k =>
      (singularDilation_isHermitian X).eigenvectorBasis j.val (Sum.inr k))) = _
  rw [singular_braket_real_scale]
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hs]
  exact singularPositive_right_half_gram X i j

/-- The actual singular-vector families reconstruct every original rectangular entry. -/
theorem singularFamily_reconstruct {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m n ℂ) (i : m) (j : n) :
    X i j = ∑ k : SingularPositiveIndex X,
      (singularWeight X k : ℂ) * singularLeft X k i * conj (singularRight X k j) := by
  classical
  rw [singularDilation_positive_cross X i j,
    hermitian_cfc_entry _ (singularDilation_isHermitian X), Finset.mul_sum]
  let w := (singularDilation_isHermitian X).eigenvalues
  let e := (singularDilation_isHermitian X).eigenvectorBasis
  have hf : (∑ k : m ⊕ n, 2 * (((max (w k) 0 : ℝ) : ℂ) * e k (Sum.inl i) * conj (e k (Sum.inr j)))) =
      ∑ k : {k : m ⊕ n // 0 < w k}, 2 * ((w k.val : ℂ) * e k.val (Sum.inl i) * conj (e k.val (Sum.inr j))) := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun k => 0 < w k))
      (by intro k; simp) (fun k => 2 * ((w k : ℂ) * e k (Sum.inl i) * conj (e k (Sum.inr j)))),
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : 0 < w k
    · simp [hk, max_eq_left hk.le]
    · simp [hk, max_eq_right (le_of_not_gt hk)]
  change (∑ k : m ⊕ n, 2 * (((max (w k) 0 : ℝ) : ℂ) * e k (Sum.inl i) * conj (e k (Sum.inr j)))) = _
  rw [hf]
  apply Finset.sum_congr rfl
  intro k _
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [singularWeight, singularLeft, singularRight, map_mul, Complex.conj_ofReal]
  dsimp [w, e]
  linear_combination -((singularDilation_isHermitian X).eigenvalues k.val : ℂ) *
    (singularDilation_isHermitian X).eigenvectorBasis k.val (Sum.inl i) *
      conj ((singularDilation_isHermitian X).eigenvectorBasis k.val (Sum.inr j)) * hs

end ThreeCopyQutritWerner
