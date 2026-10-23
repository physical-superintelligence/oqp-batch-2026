module

public import ThreeCopyQutritWerner.TwoCutPairPlanes
public import ThreeCopyQutritWerner.SharpGammaFamilyAdjoint

@[expose] public section


/-!
# Actual local output and input planes of qutrit two-site zeros

The original matrix, its rank bound and its vanishing cut form are the sole
premises. The zero matrix is included. Output and input planes are constructed
separately; this does not assume that the planes coincide.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

private theorem twoCut_reshape_ne_zero_of_norm_pos
    (x : Fin 3 × Fin 3 → ℂ) (h : 0 < vecNormSq x) : sharpReshape x ≠ 0 := by
  intro hz
  have hx : x = 0 := by
    funext ⟨i, j⟩
    exact congrFun (congrFun hz i) j
  simp [hx, vecNormSq] at h

private theorem twoCut_mul_ketBra_entry
    {n : Type*} [Fintype n] (W : Matrix n n ℂ) (x y : n → ℂ) (i j : n) :
    (W * ketBra x y) i j = (W *ᵥ x) i * conj (y j) := by
  simp only [Matrix.mul_apply, ketBra, Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Every actual rank-at-most-two qutrit cut zero has thin output support at
both sites, with the coordinate changes constructed from its original factors. -/
theorem cutForm_zero_exists_output_planes
    (C : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hC : C.rank ≤ 2) (hz : cutForm C = 0) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ a b : Fin 3,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      ∀ (i j : Fin 3) (q : Fin 3 × Fin 3), i = a ∨ j = b →
        ((U ⊗ₖ V) * C) (i, j) q = 0 := by
  by_cases hzero : C = 0
  · refine ⟨1, 1, 0, 0, by simp, by simp, ?_⟩
    simp [hzero]
  obtain ⟨x₁, x₂, y₁, y₂, he, hd, h1, h2, hg1, hg2, hτ,
    hb1, hb2, hx, hy, hpL, hpR⟩ :=
    cutForm_zero_exists_equal_orthogonal_factors C hC hz
  have hn1 : 0 < vecNormSq x₁ := by
    by_contra hn
    have hn0 : vecNormSq x₁ = 0 := le_antisymm (le_of_not_gt hn) (vecNormSq_nonneg x₁)
    have hn2 : vecNormSq x₂ = 0 := hd.symm.trans hn0
    apply hzero
    ext i j
    rw [he]
    simp only [Matrix.add_apply, ketBra, eq_zero_of_vecNormSq_eq_zero x₁ hn0 i,
      eq_zero_of_vecNormSq_eq_zero x₂ hn2 i, zero_mul, add_zero, Matrix.zero_apply]
  have hn2 : 0 < vecNormSq x₂ := hd ▸ hn1
  obtain ⟨U, V, a, b, hU, hV, hs⟩ := sharpPolarizedMinor_nonzero_pair_exists_planes
    (sharpReshape x₂) (sharpReshape x₁)
    (twoCut_reshape_ne_zero_of_norm_pos x₂ hn2)
    (twoCut_reshape_ne_zero_of_norm_pos x₁ hn1)
    ((biAnti_eq_zero_iff_sharpPolarizedMinor x₂ x₁).mp hx)
  refine ⟨U, V, a, b, hU, hV, ?_⟩
  intro i j q hij
  have ht1 : ((U ⊗ₖ V) *ᵥ x₁) (i, j) = 0 := by
    change sharpReshape ((U ⊗ₖ V) *ᵥ x₁) i j = 0
    rw [sharpReshape_kronecker_mulVec]
    rcases hij with rfl | rfl
    · exact (hs j).2.2.1
    · exact (hs i).2.2.2
  have ht2 : ((U ⊗ₖ V) *ᵥ x₂) (i, j) = 0 := by
    change sharpReshape ((U ⊗ₖ V) *ᵥ x₂) i j = 0
    rw [sharpReshape_kronecker_mulVec]
    rcases hij with rfl | rfl
    · exact (hs j).1
    · exact (hs i).2.1
  rw [he, Matrix.mul_add, Matrix.add_apply, twoCut_mul_ketBra_entry,
    twoCut_mul_ketBra_entry, ht1, ht2, zero_mul, zero_mul, add_zero]

/-- The original cut form is invariant under the actual adjoint. -/
theorem cutForm_conjTranspose {L R : Type*} [Fintype L] [Fintype R]
    (C : Matrix (L × R) (L × R) ℂ) : cutForm Cᴴ = cutForm C := by
  simp only [cutForm, sharp_ptraceL_conjTranspose, sharp_ptraceR_conjTranspose,
    rankTwo_frobSq_conjTranspose, Matrix.trace_conjTranspose, Complex.star_def,
    Complex.normSq_conj]

/-- The input planes are independently constructed by applying the same
unconditional theorem to the actual adjoint. No common-plane premise is used. -/
theorem cutForm_zero_exists_input_planes
    (C : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hC : C.rank ≤ 2) (hz : cutForm C = 0) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ a b : Fin 3,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      ∀ (i j : Fin 3) (q : Fin 3 × Fin 3), i = a ∨ j = b →
        ((U ⊗ₖ V) * Cᴴ) (i, j) q = 0 := by
  apply cutForm_zero_exists_output_planes Cᴴ
  · simpa only [Matrix.rank_conjTranspose] using hC
  · simpa only [cutForm_conjTranspose] using hz

end ThreeCopyQutritWerner
