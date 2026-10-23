module

public import ThreeCopyQutritWerner.SharpPartialTraceMinors

@[expose] public section


/-!
# Actual crossed singular-pair sharp extremizers

A gamma-one pair supplies a concrete rank-at-most-two matrix of squared
Frobenius norm two whose double-antisymmetric projection has squared norm
one. Every range vector of the actual singular pair has singular reshape.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The literal crossed difference, with ordinary tensor coefficients. -/
def sharpCrossDifference {n : Type*} (u v s t : n → ℂ) : Matrix n n ℂ :=
  sharpTensorRay u t + (-1 : ℂ) • sharpTensorRay s v

theorem sharpCrossDifference_rank_le_two {n : Type*} [Fintype n]
    (u v s t : n → ℂ) : (sharpCrossDifference u v s t).rank ≤ 2 :=
  sharpTensorRay_mix_rank_le_two u t s v (-1)

/-- Orthogonal first-family rays give the exact original squared norm two. -/
theorem sharpCrossDifference_frobSq {n : Type*} [Fintype n]
    (u v s t : n → ℂ) (hu : vecNormSq u = 1) (hv : vecNormSq v = 1)
    (hs : vecNormSq s = 1) (ht : vecNormSq t = 1) (hus : braket u s = 0) :
    frobSq (sharpCrossDifference u v s t) = 2 := by
  rw [sharpCrossDifference, frobSq_add, frobSq_smul,
    sharpTensorRay_frobSq, sharpTensorRay_frobSq,
    sharp_hsInner_smul_right, sharpTensorRay_pairing, hu, hv, hs, ht, hus]
  norm_num

/-- Full complex gamma-one equality gives exact sharp projection saturation
of the original crossed difference. -/
theorem sharpCrossDifference_projection_frobSq
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (u v s t : L × R → ℂ) (hu : vecNormSq u = 1) (hv : vecNormSq v = 1)
    (hs : vecNormSq s = 1) (ht : vecNormSq t = 1) (hus : braket u s = 0)
    (hg : sharpPartialTraceGamma u v s t = 1) :
    frobSq (sharpDoubleAnti (sharpCrossDifference u v s t)) = 1 := by
  let A := sharpTensorRay u t
  let B := sharpTensorRay s v
  have hp : (hsInner (sharpDoubleAnti A) (sharpDoubleAnti B)).re = -(1 / 4) := by
    rw [sharpPartialTraceGamma_offdiagonal u v s t hus,
      sharpDoubleAnti_pairing_projected] at hg
    have h := congrArg Complex.re hg
    norm_num [Complex.mul_re] at h
    change -(4 * (hsInner (sharpDoubleAnti A) (sharpDoubleAnti B)).re) = 1 at h
    linarith
  have hz : sharpDoubleAnti (A + B) = 0 :=
    sharpPartialTraceGamma_offdiagonal_eq_one_null u v s t hu hv hs ht hus hg
  have hsum : frobSq (sharpDoubleAnti A) + frobSq (sharpDoubleAnti B) = 1 / 2 := by
    have h := congrArg frobSq hz
    rw [sharpDoubleAnti_add, frobSq_add, hp] at h
    have hz0 : frobSq (0 : Matrix (L × R) (L × R) ℂ) = 0 := by simp [frobSq]
    rw [hz0] at h
    linarith
  change frobSq (sharpDoubleAnti (A + (-1 : ℂ) • B)) = 1
  rw [sharpDoubleAnti_add, sharpDoubleAnti_smul, frobSq_add, frobSq_smul,
    sharp_hsInner_smul_right]
  simp only [Complex.normSq_neg, Complex.normSq_one, one_mul, neg_one_mul, Complex.neg_re]
  rw [hp]
  linarith

/-- Every image of the crossed difference is an actual two-vector combination. -/
theorem sharpCrossDifference_mulVec {n : Type*} [Fintype n]
    (u v s t z : n → ℂ) :
    sharpCrossDifference u v s t *ᵥ z = fun r =>
      (∑ q, t q * z q) * u r + (-(∑ q, v q * z q)) * s r := by
  funext r
  simp only [sharpCrossDifference, sharpTensorRay, Matrix.mulVec, dotProduct,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, neg_one_mul,
    neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

/-- Actual singular rays have unit norm, including their original complex phase. -/
theorem sharpPartialTrace_singular_unit_norms
    {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (i : SingularPositiveIndex X) :
    vecNormSq (singularLeft X i) = 1 ∧ vecNormSq (singularRight X i) = 1 := by
  constructor
  · have h := singularLeft_braket X i i
    rw [if_pos rfl, braket_self] at h
    exact_mod_cast h
  · have h := singularRight_braket X i i
    rw [if_pos rfl, braket_self] at h
    exact_mod_cast h

/-- The actual singular-pair difference has rank at most two, norm squared
two and exactly saturated sharp projection. No abstract pair is supplied. -/
theorem sharpPartialTrace_singular_cross_saturation
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (X : Matrix (L × R) (L × R) ℂ)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace)
    (i j : SingularPositiveIndex X) (hij : i ≠ j) :
    let Y := sharpCrossDifference (singularLeft X i) (singularRight X i)
      (singularLeft X j) (singularRight X j)
    Y.rank ≤ 2 ∧ frobSq Y = 2 ∧ frobSq (sharpDoubleAnti Y) = frobSq Y / 2 := by
  dsimp only
  have hi := sharpPartialTrace_singular_unit_norms X i
  have hj := sharpPartialTrace_singular_unit_norms X j
  have ho : braket (singularLeft X i) (singularLeft X j) = 0 := by
    rw [singularLeft_braket, if_neg hij]
  have hn := sharpCrossDifference_frobSq _ _ _ _ hi.1 hi.2 hj.1 hj.2 ho
  refine ⟨sharpCrossDifference_rank_le_two _ _ _ _, hn, ?_⟩
  rw [hn, sharpCrossDifference_projection_frobSq _ _ _ _ hi.1 hi.2 hj.1 hj.2 ho
    (sharpPartialTrace_singular_gamma_eq_one X hsat i j)]
  norm_num

/-- Every actual range vector of a singular-pair difference has singular
three-by-three reshape, by the full common-combination minor relation. -/
theorem sharpPartialTrace_singular_cross_range_det_zero
    (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace)
    (i j : SingularPositiveIndex X) (z : Fin 3 × Fin 3 → ℂ) :
    (sharpReshape ((sharpCrossDifference (singularLeft X i) (singularRight X i)
      (singularLeft X j) (singularRight X j)) *ᵥ z)).det = 0 := by
  classical
  rw [sharpCrossDifference_mulVec]
  have h := sharpPartialTrace_singular_common_reshape_det_zero X hsat
    (fun k => (if k = i then ∑ q, singularRight X j q * z q else 0) +
      (if k = j then -(∑ q, singularRight X i q * z q) else 0))
  simpa only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

end ThreeCopyQutritWerner
