module

public import ThreeCopyQutritWerner.SharpPartialTrace
public import ThreeCopyQutritWerner.RankOne

@[expose] public section


/-!
# Polynomial consequences of sharp partial-trace equality

Positive weights make every term in the gamma deficit vanish. For actual
singular families this forces the double-antisymmetric projection to kill
each diagonal tensor ray and every polarized cross sum. The result is a
necessary equality condition, with no rank exclusion for extremizers.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- A complex number in the closed unit disk with real part one equals one. -/
theorem sharp_complex_eq_one_of_re_eq_one (z : ℂ) (hn : ‖z‖ ≤ 1) (hr : z.re = 1) :
    z = 1 := by
  have hi : z.im = 0 := by
    have hs := Complex.sq_norm_sub_sq_re z
    nlinarith [norm_nonneg z, sq_nonneg z.im]
  exact Complex.ext (by simpa only [Complex.one_re] using hr)
    (by simpa only [Complex.one_im] using hi)

/-- Equality in the positive weighted gamma bound saturates every complex
coefficient, including coefficients for distinct rays. -/
theorem sharpPartialTraceGamma_eq_one_of_weighted_saturation {ι : Type*} [Fintype ι]
    (u v : ι → L × R → ℂ) (w : ι → ℝ)
    (hu : ∀ i, vecNormSq (u i) = 1) (hv : ∀ i, vecNormSq (v i) = 1)
    (huo : ∀ i j, i ≠ j → braket (u i) (u j) = 0) (hw : ∀ i, 0 < w i)
    (hsat : frobSq (ptraceL (∑ i, (w i : ℂ) • ketBra (u i) (v i))) +
      frobSq (ptraceR (∑ i, (w i : ℂ) • ketBra (u i) (v i))) =
      (∑ i, w i) ^ 2 + Complex.normSq (∑ i, (w i : ℂ) • ketBra (u i) (v i)).trace)
    (i j : ι) : sharpPartialTraceGamma (u i) (v i) (u j) (v j) = 1 := by
  have hquad := sharpPartialTraceGamma_weighted_real u v w
  rw [hsat] at hquad
  have hprod : (∑ p, ∑ q, w p * w q) = (∑ p, w p) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]
  have hzero : (∑ p, ∑ q, w p * w q *
      (1 - (sharpPartialTraceGamma (u p) (v p) (u q) (v q)).re)) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [hprod, ← hquad]
    ring
  have hnon (p q : ι) : 0 ≤ w p * w q *
      (1 - (sharpPartialTraceGamma (u p) (v p) (u q) (v q)).re) :=
    mul_nonneg (mul_pos (hw p) (hw q)).le
      (sub_nonneg.mpr (sharpPartialTraceGamma_family_re_le u v hu hv huo p q))
  have hrow := congrFun ((Fintype.sum_eq_zero_iff_of_nonneg
    (fun p => Finset.sum_nonneg fun q _ => hnon p q)).mp hzero) i
  have hentry := congrFun ((Fintype.sum_eq_zero_iff_of_nonneg (hnon i)).mp hrow) j
  have hre : (sharpPartialTraceGamma (u i) (v i) (u j) (v j)).re = 1 := by
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hentry).resolve_left
      (ne_of_gt (mul_pos (hw i) (hw j))))).symm
  exact sharp_complex_eq_one_of_re_eq_one _
    (sharpPartialTraceGamma_family_norm_le u v hu hv huo i j) hre

/-- A saturated diagonal gamma kills the literal double-antisymmetric tensor ray. -/
theorem sharpPartialTraceGamma_diagonal_eq_one_null (u v : L × R → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1)
    (hgamma : sharpPartialTraceGamma u v u v = 1) :
    sharpDoubleAnti (sharpTensorRay u v) = 0 := by
  have h := congrArg Complex.re hgamma
  rw [sharpPartialTraceGamma_diagonal u v hu hv, Complex.ofReal_re, Complex.one_re] at h
  apply matrix_eq_zero_of_frobSq_eq_zero
  linarith

/-- A saturated off-diagonal gamma kills the polarized crossed tensor.
The bound is applied to the difference of two orthogonal tensor rays. -/
theorem sharpPartialTraceGamma_offdiagonal_eq_one_null (u v s t : L × R → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1)
    (hs : vecNormSq s = 1) (ht : vecNormSq t = 1)
    (hus : braket u s = 0) (hgamma : sharpPartialTraceGamma u v s t = 1) :
    sharpDoubleAnti (sharpTensorRay u t + sharpTensorRay s v) = 0 := by
  let A := sharpTensorRay u t
  let B := sharpTensorRay s v
  have hA : frobSq A = 1 := by rw [sharpTensorRay_frobSq, hu, ht, one_mul]
  have hB : frobSq B = 1 := by rw [sharpTensorRay_frobSq, hs, hv, one_mul]
  have hAB : hsInner A B = 0 := by rw [sharpTensorRay_pairing, hus, zero_mul]
  have hpair : (hsInner (sharpDoubleAnti A) (sharpDoubleAnti B)).re = -(1 / 4) := by
    rw [sharpPartialTraceGamma_offdiagonal u v s t hus,
      sharpDoubleAnti_pairing_projected] at hgamma
    have h := congrArg Complex.re hgamma
    norm_num [Complex.mul_re] at h
    change -(4 * (hsInner (sharpDoubleAnti A) (sharpDoubleAnti B)).re) = 1 at h
    linarith
  have hnorm : frobSq (A + (-1 : ℂ) • B) = 2 := by
    rw [frobSq_add, frobSq_smul, hA, hB, sharp_hsInner_smul_right, hAB]
    norm_num
  have hbound := sharpDoubleAnti_rank_two_bound (A + (-1 : ℂ) • B)
    (sharpTensorRay_mix_rank_le_two u t s v (-1))
  rw [hnorm, sharpDoubleAnti_add, sharpDoubleAnti_smul, frobSq_add,
    frobSq_smul, sharp_hsInner_smul_right] at hbound
  simp only [Complex.normSq_neg, Complex.normSq_one, one_mul, neg_one_mul,
    Complex.neg_re] at hbound
  rw [hpair] at hbound
  apply matrix_eq_zero_of_frobSq_eq_zero
  rw [sharpDoubleAnti_add, frobSq_add, hpair]
  have hnon := frobSq_nonneg (sharpDoubleAnti (A + B))
  rw [sharpDoubleAnti_add, frobSq_add, hpair] at hnon
  change frobSq (sharpDoubleAnti A) + frobSq (sharpDoubleAnti B) + 2 * (-(1 / 4)) = 0
  linarith

/-- Every gamma coefficient of the actual strictly positive singular family
saturates when the original matrix saturates the sharp partial-trace inequality. -/
theorem sharpPartialTrace_singular_gamma_eq_one
    (X : Matrix (L × R) (L × R) ℂ)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace)
    (i j : SingularPositiveIndex X) :
    sharpPartialTraceGamma (singularLeft X i) (singularRight X i)
      (singularLeft X j) (singularRight X j) = 1 := by
  have hu (k : SingularPositiveIndex X) : vecNormSq (singularLeft X k) = 1 := by
    have h := singularLeft_braket X k k
    rw [if_pos rfl, braket_self] at h
    exact_mod_cast h
  have hv (k : SingularPositiveIndex X) : vecNormSq (singularRight X k) = 1 := by
    have h := singularRight_braket X k k
    rw [if_pos rfl, braket_self] at h
    exact_mod_cast h
  have ho (k l : SingularPositiveIndex X) (hkl : k ≠ l) :
      braket (singularLeft X k) (singularLeft X l) = 0 := by
    rw [singularLeft_braket, if_neg hkl]
  have he : X = ∑ k : SingularPositiveIndex X,
      (singularWeight X k : ℂ) • ketBra (singularLeft X k) (singularRight X k) := by
    ext r s
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ketBra, mul_assoc] using
      singularFamily_reconstruct X r s
  apply sharpPartialTraceGamma_eq_one_of_weighted_saturation
    (singularLeft X) (singularRight X) (singularWeight X) hu hv ho (singularWeight_pos X)
  rw [← he, ← nuclearTrace_eq_sum_singularWeight X]
  exact hsat

/-- Sharp partial-trace equality forces all diagonal and polarized singular
tensor relations, without excluding singular ranks three or higher. -/
theorem sharpPartialTrace_singular_polarized_null
    (X : Matrix (L × R) (L × R) ℂ)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace)
    (i j : SingularPositiveIndex X) :
    sharpDoubleAnti (sharpTensorRay (singularLeft X i) (singularRight X j) +
      sharpTensorRay (singularLeft X j) (singularRight X i)) = 0 := by
  have hu (k : SingularPositiveIndex X) : vecNormSq (singularLeft X k) = 1 := by
    have h := singularLeft_braket X k k
    rw [if_pos rfl, braket_self] at h
    exact_mod_cast h
  have hv (k : SingularPositiveIndex X) : vecNormSq (singularRight X k) = 1 := by
    have h := singularRight_braket X k k
    rw [if_pos rfl, braket_self] at h
    exact_mod_cast h
  by_cases hij : i = j
  · subst j
    have h := sharpPartialTraceGamma_diagonal_eq_one_null _ _ (hu i) (hv i)
      (sharpPartialTrace_singular_gamma_eq_one X hsat i i)
    rw [sharpDoubleAnti_add, h, add_zero]
  · exact sharpPartialTraceGamma_offdiagonal_eq_one_null _ _ _ _
      (hu i) (hv i) (hu j) (hv j) (by rw [singularLeft_braket, if_neg hij])
      (sharpPartialTrace_singular_gamma_eq_one X hsat i j)

/-- The replica projection commutes with any finite matrix sum. -/
theorem sharpDoubleAnti_sum {ι : Type*} [Fintype ι]
    (A : ι → Matrix (L × R) (L × R) ℂ) :
    sharpDoubleAnti (∑ i, A i) = ∑ i, sharpDoubleAnti (A i) := by
  ext r s
  simp only [sharpDoubleAnti, sharpSwapLeft, sharpSwapRight, Matrix.sum_apply,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]

/-- The coefficient tensor of two combinations retains their full double sum. -/
theorem sharpTensorRay_common_weighted_sum {ι : Type*} [Fintype ι]
    (u v : ι → L × R → ℂ) (z : ι → ℂ) :
    sharpTensorRay (fun r => ∑ i, z i * u i r) (fun r => ∑ i, z i * v i r) =
      ∑ i, ∑ j, (z i * z j) • sharpTensorRay (u i) (v j) := by
  ext r s
  simp only [sharpTensorRay, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- All polarized tensor relations imply the full common-coefficient polynomial
null identity; the coefficients can be arbitrary complex numbers. -/
theorem sharpDoubleAnti_common_combination_null {ι : Type*} [Fintype ι]
    (u v : ι → L × R → ℂ)
    (hpair : ∀ i j, sharpDoubleAnti
      (sharpTensorRay (u i) (v j) + sharpTensorRay (u j) (v i)) = 0)
    (z : ι → ℂ) :
    sharpDoubleAnti (sharpTensorRay (fun r => ∑ i, z i * u i r)
      (fun r => ∑ i, z i * v i r)) = 0 := by
  classical
  have hp (i j : ι) : sharpDoubleAnti (sharpTensorRay (u i) (v j)) +
      sharpDoubleAnti (sharpTensorRay (u j) (v i)) = 0 := by
    rw [← sharpDoubleAnti_add, hpair i j]
  have hsum : (∑ i, ∑ j, (z i * z j) •
      (sharpDoubleAnti (sharpTensorRay (u i) (v j)) +
        sharpDoubleAnti (sharpTensorRay (u j) (v i)))) = 0 := by
    simp only [hp, smul_zero, Finset.sum_const_zero]
  have hswap : (∑ i, ∑ j, (z i * z j) • sharpDoubleAnti (sharpTensorRay (u j) (v i))) =
      ∑ i, ∑ j, (z i * z j) • sharpDoubleAnti (sharpTensorRay (u i) (v j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (z j) (z i)]
  simp only [smul_add, Finset.sum_add_distrib] at hsum
  rw [hswap] at hsum
  rw [sharpTensorRay_common_weighted_sum]
  simp_rw [sharpDoubleAnti_sum, sharpDoubleAnti_smul]
  ext r s
  have h := congrFun (congrFun hsum r) s
  change _ + _ = (0 : ℂ) at h
  change (∑ i, ∑ j, (z i * z j) •
    sharpDoubleAnti (sharpTensorRay (u i) (v j))) r s = 0
  linear_combination h / 2

/-- Every sharp-PT extremizer supplies an actual pair of singular linear maps
whose common complex combinations satisfy the two-copy null polynomial. -/
theorem sharpPartialTrace_singular_common_combination_null
    (X : Matrix (L × R) (L × R) ℂ)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace)
    (z : SingularPositiveIndex X → ℂ) :
    sharpDoubleAnti (sharpTensorRay
      (fun r => ∑ i, z i * singularLeft X i r)
      (fun r => ∑ i, z i * singularRight X i r)) = 0 :=
  sharpDoubleAnti_common_combination_null (singularLeft X) (singularRight X)
    (sharpPartialTrace_singular_polarized_null X hsat) z

end ThreeCopyQutritWerner
