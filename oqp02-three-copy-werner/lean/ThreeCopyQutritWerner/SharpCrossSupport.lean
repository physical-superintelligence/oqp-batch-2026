module

public import ThreeCopyQutritWerner.SharpPartialTracePairSaturation
public import ThreeCopyQutritWerner.SharpQutritThinRows

@[expose] public section


/-!
# Recovering the four actual vectors from crossed-pair support

The congruence transforms ordinary tensor factors by the same matrix. Exact
orthonormal contractions recover both factors of each family, so matrix
row-and-column support gives support of all four actual singular vectors.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Kronecker

namespace ThreeCopyQutritWerner

/-- Ordinary tensor congruence acts on both original vector factors. -/
theorem sharpTensorRay_congruence {n : Type*} [Fintype n]
    (W : Matrix n n ℂ) (u v : n → ℂ) :
    W * sharpTensorRay u v * Wᵀ = sharpTensorRay (W *ᵥ u) (W *ᵥ v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, sharpTensorRay,
    Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem sharpCrossDifference_congruence {n : Type*} [Fintype n]
    (W : Matrix n n ℂ) (u v s t : n → ℂ) :
    W * sharpCrossDifference u v s t * Wᵀ =
      sharpCrossDifference (W *ᵥ u) (W *ᵥ v) (W *ᵥ s) (W *ᵥ t) := by
  simp only [sharpCrossDifference, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, sharpTensorRay_congruence]

/-- Orthogonal second-family contractions recover both first-family row entries. -/
theorem sharpCrossDifference_zero_row {n : Type*} [Fintype n]
    (u v s t : n → ℂ) (hv : braket v v = 1) (ht : braket t t = 1)
    (hvt : braket v t = 0) (r : n)
    (hz : ∀ p, sharpCrossDifference u v s t r p = 0) : u r = 0 ∧ s r = 0 := by
  have htv : braket t v = 0 := by rw [← conj_braket, hvt, map_zero]
  have himage (z : n → ℂ) : (sharpCrossDifference u v s t *ᵥ z) r = 0 := by
    simp [Matrix.mulVec, dotProduct, hz]
  have hu := himage (fun p => conj (t p))
  have hs := himage (fun p => conj (v p))
  rw [sharpCrossDifference_mulVec] at hu hs
  have htt : (∑ p, t p * conj (t p)) = 1 := by simpa only [braket, mul_comm] using ht
  have hvv : (∑ p, v p * conj (v p)) = 1 := by simpa only [braket, mul_comm] using hv
  have htv' : (∑ p, t p * conj (v p)) = 0 := by simpa only [braket, mul_comm] using hvt
  have hvt' : (∑ p, v p * conj (t p)) = 0 := by simpa only [braket, mul_comm] using htv
  simp only [htt, hvt', htv', hvv, one_mul, zero_mul, neg_zero,
    zero_add, add_zero, neg_one_mul] at hu hs
  exact ⟨hu, neg_eq_zero.mp hs⟩

/-- Row and column annihilation recover all four original vector entries. -/
theorem sharpCrossDifference_zero_row_column {n : Type*} [Fintype n]
    (u v s t : n → ℂ)
    (hu : braket u u = 1) (hs : braket s s = 1) (hus : braket u s = 0)
    (hv : braket v v = 1) (ht : braket t t = 1) (hvt : braket v t = 0)
    (r : n) (hz : ∀ p, sharpCrossDifference u v s t r p = 0 ∧
      sharpCrossDifference u v s t p r = 0) :
    u r = 0 ∧ s r = 0 ∧ v r = 0 ∧ t r = 0 := by
  have hleft := sharpCrossDifference_zero_row u v s t hv ht hvt r (fun p => (hz p).1)
  have hsu : braket s u = 0 := by rw [← conj_braket, hus, map_zero]
  have hright := sharpCrossDifference_zero_row t s v u hs hu hsu r (fun p => by
    have h := (hz p).2
    simpa only [sharpCrossDifference, sharpTensorRay, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, mul_comm] using h)
  exact ⟨hleft.1, hleft.2, hright.2, hright.1⟩

/-- Each distinct pair of actual singular rays of a sharp-PT extremizer
has a common physical two-by-two support, simultaneously for both families. -/
theorem sharpPartialTrace_singular_pair_exists_thin_coordinates
    (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace)
    (i j : SingularPositiveIndex X) (hij : i ≠ j) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧ ∀ r s : Fin 3, r = a ∨ s = a →
        ((U ⊗ₖ V) *ᵥ singularLeft X i) (r, s) = 0 ∧
        ((U ⊗ₖ V) *ᵥ singularLeft X j) (r, s) = 0 ∧
        ((U ⊗ₖ V) *ᵥ singularRight X i) (r, s) = 0 ∧
        ((U ⊗ₖ V) *ᵥ singularRight X j) (r, s) = 0 := by
  let Y := sharpCrossDifference (singularLeft X i) (singularRight X i)
    (singularLeft X j) (singularRight X j)
  have hY := sharpPartialTrace_singular_cross_saturation X hsat i j hij
  obtain ⟨U, V, a, hU, hV, hsupport⟩ := sharpDoubleAnti_saturation_exists_thin_normal Y
    hY.1 hY.2.2 (by change 0 < frobSq Y; rw [hY.2.1]; norm_num)
    (sharpPartialTrace_singular_cross_range_det_zero X hsat i j)
  have hW := sharpLocalCongruence_unitary U V hU hV
  refine ⟨U, V, a, hU, hV, ?_⟩
  intro r s hrs
  apply sharpCrossDifference_zero_row_column
    ((U ⊗ₖ V) *ᵥ singularLeft X i) ((U ⊗ₖ V) *ᵥ singularRight X i)
    ((U ⊗ₖ V) *ᵥ singularLeft X j) ((U ⊗ₖ V) *ᵥ singularRight X j)
  · rw [singular_braket_isometry _ hW, singularLeft_braket, if_pos rfl]
  · rw [singular_braket_isometry _ hW, singularLeft_braket, if_pos rfl]
  · rw [singular_braket_isometry _ hW, singularLeft_braket, if_neg hij]
  · rw [singular_braket_isometry _ hW, singularRight_braket, if_pos rfl]
  · rw [singular_braket_isometry _ hW, singularRight_braket, if_pos rfl]
  · rw [singular_braket_isometry _ hW, singularRight_braket, if_neg hij]
  · intro p
    simpa only [Y, sharpCrossDifference_congruence] using hsupport r s p hrs

end ThreeCopyQutritWerner
