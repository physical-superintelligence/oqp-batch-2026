module

public import ThreeCopyQutritWerner.ThinSingleOutputTransport
public import ThreeCopyQutritWerner.TwoCutSwap

@[expose] public section


/-! Swapped physical conjugation and propagation of arbitrary anchor zero rows. -/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem twoCutSwap_local_conj
    (U V : Matrix (Fin 3) (Fin 3) ℂ)
    (A : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    twoCutSwap ((U ⊗ₖ V) * A * (U ⊗ₖ V)ᴴ) =
      (V ⊗ₖ U) * twoCutSwap A * (V ⊗ₖ U)ᴴ := by
  let e := Equiv.prodComm (Fin 3) (Fin 3)
  have hW : (U ⊗ₖ V).submatrix e e = V ⊗ₖ U := by
    ext p q
    simp only [e, Matrix.submatrix_apply, Equiv.prodComm_apply, Matrix.kroneckerMap_apply, Prod.swap]
    ring
  have hH : ((U ⊗ₖ V)ᴴ).submatrix e e = (V ⊗ₖ U)ᴴ := by
    rw [← Matrix.conjTranspose_submatrix, hW]
  change ((U ⊗ₖ V) * A * (U ⊗ₖ V)ᴴ).submatrix e e = _
  rw [← Matrix.submatrix_mul_equiv ((U ⊗ₖ V) * A) (U ⊗ₖ V)ᴴ e e e,
    ← Matrix.submatrix_mul_equiv (U ⊗ₖ V) A e e e, hW, hH]
  rfl

theorem single_output_anchor_zero_row_propagates
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (k j₀ : a)
    (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0)
    (hne : firstSiteBlock C k j₀ ≠ 0) (p : b × c)
    (hanchor : ∀ q, firstSiteBlock C k j₀ p q = 0) :
    ∀ i q, C (i, p) q = 0 := by
  intro i q
  by_cases hi : i = k
  · subst i
    by_cases hq : firstSiteBlock C k q.1 = 0
    · exact congrFun (congrFun hq p) q.2
    · have hR := (single_output_nonzero_blocks_same_range C hC hz k hrow
        q.1 j₀ hq hne).2.2.le
      obtain ⟨R, hR⟩ := matrix_exists_right_factor_of_range_le
        (firstSiteBlock C k q.1) (firstSiteBlock C k j₀) hR
      have he := congrFun (congrFun hR p) q.2
      rw [Matrix.mul_apply] at he
      simp only [hanchor, zero_mul, Finset.sum_const_zero] at he
      simpa only [firstSiteBlock, Matrix.submatrix_apply, Prod.mk.eta] using he
  · exact hrow i hi p q

end ThreeCopyQutritWerner
