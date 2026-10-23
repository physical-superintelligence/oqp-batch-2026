module

public import ThreeCopyQutritWerner.AffinePencilRankDrop
public import ThreeCopyQutritWerner.SharpRankOneFamily

@[expose] public section


/-!
# The two genuine branches of a rank-one affine pencil

The original rectangular coefficient matrices have either a common nonzero
column factor or a common nonzero row factor, apart from the all-zero pencil.
In particular, pointwise rank one does not imply one fixed range line.
Existing product-minor algebra is reused without normalization assumptions.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

variable {m n : Type*} [Fintype m] [Fintype n]

theorem matrix_entry_minor_zero_of_rank_le_one (A : Matrix m n ℂ)
    (hA : A.rank ≤ 1) (i j : m) (k l : n) :
    A i k * A j l - A i l * A j k = 0 := by
  by_contra h
  have ht := matrix_two_le_rank_of_entry_minor_ne_zero A i j k l h
  omega

/-- Values at zero, one and minus one recover the quadratic leading minors. -/
theorem matrix_rank_le_one_of_rank_one_plus_minus
    (A B : Matrix m n ℂ) (hA : A.rank ≤ 1)
    (hp : (A + B).rank ≤ 1) (hm : (A - B).rank ≤ 1) : B.rank ≤ 1 := by
  apply matrix_rank_le_one_of_two_minors_zero
  intro i j k l
  have h0 := matrix_entry_minor_zero_of_rank_le_one A hA i j k l
  have h1 := matrix_entry_minor_zero_of_rank_le_one (A + B) hp i j k l
  have hn := matrix_entry_minor_zero_of_rank_le_one (A - B) hm i j k l
  simp only [Matrix.add_apply, Matrix.sub_apply] at h1 hn
  apply sub_eq_zero.mp
  linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * hn - h0

/-- Actual rectangular rank-one matrices have an ordinary product factorization. -/
theorem matrix_exists_vecMulVec_of_rank_le_one (A : Matrix m n ℂ)
    (hA : A.rank ≤ 1) : ∃ u : m → ℂ, ∃ v : n → ℂ, A = Matrix.vecMulVec u v := by
  obtain ⟨X, B, hXB⟩ := (rank_le_iff_exists_mul A 1).mp hA
  refine ⟨fun i => X i 0, fun j => B 0 j, ?_⟩
  rw [hXB]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.vecMulVec_apply]

/-- Rank-one coefficients whose sum is rank one share a factor. Both alternatives
are retained, including the varying-range, fixed-row-factor case. -/
theorem matrix_rank_one_pair_common_factor (A B : Matrix m n ℂ)
    (hA : A.rank ≤ 1) (hB : B.rank ≤ 1) (hAB : (A + B).rank ≤ 1)
    (hne : A ≠ 0 ∨ B ≠ 0) :
    (∃ u : m → ℂ, ∃ v w : n → ℂ, u ≠ 0 ∧
      A = Matrix.vecMulVec u v ∧ B = Matrix.vecMulVec u w) ∨
    (∃ v : n → ℂ, ∃ u w : m → ℂ, v ≠ 0 ∧
      A = Matrix.vecMulVec u v ∧ B = Matrix.vecMulVec w v) := by
  classical
  obtain ⟨x, y, hBxy⟩ := matrix_exists_vecMulVec_of_rank_le_one B hB
  by_cases hAz : A = 0
  · have hBn : B ≠ 0 := hne.resolve_left (not_not.mpr hAz)
    have hxn : x ≠ 0 := by
      intro hz
      apply hBn
      simp only [hBxy, hz, Matrix.zero_vecMulVec]
    refine Or.inl ⟨x, 0, y, hxn, ?_, hBxy⟩
    rw [hAz]
    ext i j
    simp only [Matrix.zero_apply, Matrix.vecMulVec_apply, Pi.zero_apply, mul_zero]
  obtain ⟨u, v, hAuv⟩ := matrix_exists_vecMulVec_of_rank_le_one A hA
  obtain ⟨a, b, hsum⟩ := matrix_exists_vecMulVec_of_rank_le_one (A + B) hAB
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hAz (by ext i j; exact hn i j)
  have huv : u i * v j ≠ 0 := by simpa only [hAuv, Matrix.vecMulVec_apply] using hij
  have hu : ∃ i, u i ≠ 0 := ⟨i, left_ne_zero_of_mul huv⟩
  have hv : ∃ j, v j ≠ 0 := ⟨j, right_ne_zero_of_mul huv⟩
  have hu0 : u ≠ 0 := by
    intro hz
    exact (left_ne_zero_of_mul huv) (congrFun hz i)
  have hv0 : v ≠ 0 := by
    intro hz
    exact (right_ne_zero_of_mul huv) (congrFun hz j)
  have hp : ∀ i j, u i * v j + x i * y j = a i * b j := by
    intro i j
    have h := congrFun (congrFun hsum i) j
    simpa only [hAuv, hBxy, Matrix.add_apply, Matrix.vecMulVec_apply] using h
  have hor : TwoPlane.IsMultiple u x ∨ TwoPlane.IsMultiple v y := by
    by_contra! hn
    exact TwoPlane.not_product_of_minors u x v y
      (TwoPlane.exists_minor_ne_zero _ _ hu hn.1)
      (TwoPlane.exists_minor_ne_zero _ _ hv hn.2) a b hp
  rcases hor with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine Or.inl ⟨u, v, fun j => c * y j, hu0, hAuv, ?_⟩
    ext i j
    simp only [hBxy, Matrix.vecMulVec_apply, hc]
    ring
  · refine Or.inr ⟨v, u, fun i => c * x i, hv0, hAuv, ?_⟩
    ext i j
    simp only [hBxy, Matrix.vecMulVec_apply, hc]
    ring

/-- Complete unnormalized affine-pencil dichotomy, with all zero cases explicit.
No common-range conclusion is drawn from the fixed-row-factor branch. -/
theorem affinePencil_rank_le_one_common_factor (A B : Matrix m n ℂ)
    (hr : ∀ z : ℂ, (A + z • B).rank ≤ 1) :
    (A = 0 ∧ B = 0) ∨
    (∃ u : m → ℂ, ∃ v w : n → ℂ, u ≠ 0 ∧
      A = Matrix.vecMulVec u v ∧ B = Matrix.vecMulVec u w) ∨
    (∃ v : n → ℂ, ∃ u w : m → ℂ, v ≠ 0 ∧
      A = Matrix.vecMulVec u v ∧ B = Matrix.vecMulVec w v) := by
  by_cases hz : A = 0 ∧ B = 0
  · exact Or.inl hz
  have hA : A.rank ≤ 1 := by simpa only [zero_smul, add_zero] using hr 0
  have hp : (A + B).rank ≤ 1 := by simpa only [one_smul] using hr 1
  have hm : (A - B).rank ≤ 1 := by simpa only [neg_one_smul, sub_eq_add_neg] using hr (-1)
  have hB := matrix_rank_le_one_of_rank_one_plus_minus A B hA hp hm
  exact Or.inr (matrix_rank_one_pair_common_factor A B hA hB hp (not_and_or.mp hz))

end ThreeCopyQutritWerner
