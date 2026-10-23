module

public import ThreeCopyQutritWerner.ThinSingleOutputRange
public import ThreeCopyQutritWerner.MatrixRangeFactor

@[expose] public section


/-! Literal block transport and propagation of an anchor's local output coordinate. -/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem firstSiteBlock_conj_remaining
    {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a]
    (C : Matrix (a × d) (a × d) ℂ) (W : Matrix d d ℂ) (i j : a) :
    firstSiteBlock (((1 : Matrix a a ℂ) ⊗ₖ W) * C * ((1 : Matrix a a ℂ) ⊗ₖ W)ᴴ) i j =
      W * firstSiteBlock C i j * Wᴴ := by
  ext r s
  simp [firstSiteBlock, Matrix.submatrix_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, ite_mul, mul_ite, apply_ite]

/-- Local conjugation on the remaining two sites preserves the literal
original first output coordinate. No unitarity hypothesis is needed. -/
theorem first_output_coordinate_conj_remaining
    {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a]
    (C : Matrix (a × d) (a × d) ℂ) (W : Matrix d d ℂ) (k : a)
    (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0) :
    ∀ i, i ≠ k → ∀ r q,
      (((1 : Matrix a a ℂ) ⊗ₖ W) * C * ((1 : Matrix a a ℂ) ⊗ₖ W)ᴴ) (i, r) q = 0 := by
  intro i hi r q
  have hz : firstSiteBlock C i q.1 = 0 := by
    ext s t
    exact hrow i hi s (q.1, t)
  have he := congrFun (congrFun (firstSiteBlock_conj_remaining C W i q.1) r) q.2
  rw [hz, Matrix.mul_zero, Matrix.zero_mul] at he
  simpa only [Matrix.zero_apply, firstSiteBlock, Matrix.submatrix_apply,
    Prod.mk.eta] using he

/-- An actual anchor coordinate annihilates the entire common source,
so every original block has that same local output coordinate. -/
theorem single_output_anchor_coordinate_propagates
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (k j₀ : a) (l : b)
    (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0)
    (hne : firstSiteBlock C k j₀ ≠ 0)
    (hanchor : ∀ j, j ≠ l → ∀ r q, firstSiteBlock C k j₀ (j, r) q = 0) :
    ∀ j, j ≠ l → ∀ i r q, C (i, j, r) q = 0 := by
  intro j hj i r q
  by_cases hi : i = k
  · subst i
    by_cases hq : firstSiteBlock C k q.1 = 0
    · exact congrFun (congrFun hq (j, r)) q.2
    · have hR := (single_output_nonzero_blocks_same_range C hC hz k hrow
        q.1 j₀ hq hne).2.2.le
      obtain ⟨R, hR⟩ := matrix_exists_right_factor_of_range_le
        (firstSiteBlock C k q.1) (firstSiteBlock C k j₀) hR
      have he := congrFun (congrFun hR (j, r)) q.2
      rw [Matrix.mul_apply] at he
      simp only [hanchor j hj r, zero_mul, Finset.sum_const_zero] at he
      simpa only [firstSiteBlock, Matrix.submatrix_apply, Prod.mk.eta] using he
  · exact hrow i hi (j, r) q

end ThreeCopyQutritWerner
