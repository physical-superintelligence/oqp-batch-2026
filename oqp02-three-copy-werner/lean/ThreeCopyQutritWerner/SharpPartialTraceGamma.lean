module

public import ThreeCopyQutritWerner.SharpProjectionCross

@[expose] public section


/-!
# The literal partial-trace cross coefficients

The swap identity is proved on the original finite contractions and coefficient
tensor rays. The sharp rank-two projection bound controls all diagonal and
off-diagonal coefficients by one, as required by the SVD summation argument.
No partial-trace inequality or singular-value identity is a premise here.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

section SwapIdentity

variable {L R : Type*} [Fintype L] [Fintype R]

/-- The exact complex cross coefficient in the quadratic partial-trace estimate. -/
def sharpPartialTraceGamma (u v s t : L × R → ℂ) : ℂ :=
  ptraceInner (ketBra u v) (ketBra s t) -
    conj ((ketBra u v).trace) * (ketBra s t).trace

/-- The first literal partial trace is the crossed left-replica swap pairing. -/
theorem sharpTensorRay_swapLeft_ptrace (u v s t : L × R → ℂ) :
    hsInner (sharpTensorRay u t) (sharpSwapLeft (sharpTensorRay s v)) =
      hsInner (ptraceL (ketBra u v)) (ptraceL (ketBra s t)) := by
  rw [hsInner_ptraceL_ketBra]
  simp only [hsInner, sharpTensorRay, sharpSwapLeft, Fintype.sum_prod_type]
  rw [sum_perm_lrlr]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  simp only [map_mul]
  ring

/-- The second literal partial trace is the crossed right-replica swap pairing. -/
theorem sharpTensorRay_swapRight_ptrace (u v s t : L × R → ℂ) :
    hsInner (sharpTensorRay u t) (sharpSwapRight (sharpTensorRay s v)) =
      hsInner (ptraceR (ketBra u v)) (ptraceR (ketBra s t)) := by
  rw [hsInner_ptraceR_ketBra]
  simp only [hsInner, sharpTensorRay, sharpSwapRight, Fintype.sum_prod_type]
  rw [sum_perm_llrr]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro q _
  simp only [map_mul]
  ring

/-- Full replica exchange supplies exactly the conjugated trace product. -/
theorem sharpTensorRay_transpose_trace (u v s t : L × R → ℂ) :
    hsInner (sharpTensorRay u t) (sharpTensorRay s v)ᵀ =
      conj ((ketBra u v).trace) * (ketBra s t).trace := by
  have hT : (sharpTensorRay s v)ᵀ = sharpTensorRay v s := by
    ext i j
    exact mul_comm _ _
  rw [hT, sharpTensorRay_pairing, trace_ketBra, trace_ketBra, conj_braket]

/-- The complementary replica operator is the literal I−4Q in pairings. -/
theorem sharpDoubleAnti_complement_pairing (A B : Matrix (L × R) (L × R) ℂ) :
    hsInner A B - 4 * hsInner A (sharpDoubleAnti B) =
      hsInner A (sharpSwapLeft B) + hsInner A (sharpSwapRight B) - hsInner A Bᵀ := by
  simp only [hsInner, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [sharpDoubleAnti, Matrix.transpose_apply]
  ring

/-- Wu--Zou's swap identity in the exact crossed tensor convention. -/
theorem sharpPartialTraceGamma_eq_projection (u v s t : L × R → ℂ) :
    sharpPartialTraceGamma u v s t =
      hsInner (sharpTensorRay u t) (sharpTensorRay s v) -
        4 * hsInner (sharpTensorRay u t) (sharpDoubleAnti (sharpTensorRay s v)) := by
  rw [sharpDoubleAnti_complement_pairing, sharpTensorRay_swapLeft_ptrace,
    sharpTensorRay_swapRight_ptrace, sharpTensorRay_transpose_trace]
  rfl

/-- Projection expectations are exactly real Frobenius squares. -/
theorem sharpDoubleAnti_pairing_self_complex (A : Matrix (L × R) (L × R) ℂ) :
    hsInner A (sharpDoubleAnti A) = (frobSq (sharpDoubleAnti A) : ℂ) := by
  classical
  rw [sharpDoubleAnti_pairing_projected]
  exact (ofReal_frobSq _).symm

/-- On a diagonal singular ray the constant term is exactly one. -/
theorem sharpPartialTraceGamma_diagonal (u v : L × R → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) :
    sharpPartialTraceGamma u v u v =
      ((1 - 4 * frobSq (sharpDoubleAnti (sharpTensorRay u v)) : ℝ) : ℂ) := by
  rw [sharpPartialTraceGamma_eq_projection, sharpTensorRay_pairing, braket_self,
    braket_self, hu, hv, sharpDoubleAnti_pairing_self_complex]
  push_cast
  ring

end SwapIdentity

section CoefficientBound

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- The diagonal gamma coefficient has modulus at most one. -/
theorem sharpPartialTraceGamma_diagonal_norm_le (u v : L × R → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) :
    ‖sharpPartialTraceGamma u v u v‖ ≤ 1 := by
  have hr : (sharpTensorRay u v).rank ≤ 2 := by
    simpa only [zero_smul, add_zero] using sharpTensorRay_mix_rank_le_two u v u v 0
  have hb := sharpDoubleAnti_rank_two_bound (sharpTensorRay u v) hr
  rw [sharpTensorRay_frobSq, hu, hv] at hb
  have hn := frobSq_nonneg (sharpDoubleAnti (sharpTensorRay u v))
  rw [sharpPartialTraceGamma_diagonal u v hu hv, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith

/-- Off the diagonal the crossed tensor inner product vanishes, leaving exactly −4Q. -/
theorem sharpPartialTraceGamma_offdiagonal (u v s t : L × R → ℂ)
    (hus : braket u s = 0) :
    sharpPartialTraceGamma u v s t =
      -4 * hsInner (sharpTensorRay u t) (sharpDoubleAnti (sharpTensorRay s v)) := by
  rw [sharpPartialTraceGamma_eq_projection, sharpTensorRay_pairing, hus, zero_mul]
  ring

/-- The off-diagonal quarter bound gives the exact gamma modulus bound. -/
theorem sharpPartialTraceGamma_offdiagonal_norm_le (u v s t : L × R → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1)
    (hs : vecNormSq s = 1) (ht : vecNormSq t = 1) (hus : braket u s = 0) :
    ‖sharpPartialTraceGamma u v s t‖ ≤ 1 := by
  have h := sharpDoubleAnti_cross_norm_le_quarter u t s v hu ht hs hv hus
  rw [sharpPartialTraceGamma_offdiagonal u v s t hus, norm_mul]
  norm_num
  linarith

/-- All coefficients for separately normalized rays and an orthonormal left family
have modulus at most one. The singular-value application satisfies these premises. -/
theorem sharpPartialTraceGamma_family_norm_le {ι : Type*}
    (u v : ι → L × R → ℂ)
    (hu : ∀ i, vecNormSq (u i) = 1) (hv : ∀ i, vecNormSq (v i) = 1)
    (huo : ∀ i j, i ≠ j → braket (u i) (u j) = 0) (i j : ι) :
    ‖sharpPartialTraceGamma (u i) (v i) (u j) (v j)‖ ≤ 1 := by
  by_cases hij : i = j
  · subst j
    exact sharpPartialTraceGamma_diagonal_norm_le (u i) (v i) (hu i) (hv i)
  · exact sharpPartialTraceGamma_offdiagonal_norm_le (u i) (v i) (u j) (v j)
      (hu i) (hv i) (hu j) (hv j) (huo i j hij)

/-- The real-part bound needed by the positive singular-weight double sum. -/
theorem sharpPartialTraceGamma_family_re_le {ι : Type*}
    (u v : ι → L × R → ℂ)
    (hu : ∀ i, vecNormSq (u i) = 1) (hv : ∀ i, vecNormSq (v i) = 1)
    (huo : ∀ i j, i ≠ j → braket (u i) (u j) = 0) (i j : ι) :
    (sharpPartialTraceGamma (u i) (v i) (u j) (v j)).re ≤ 1 :=
  (Complex.re_le_norm _).trans (sharpPartialTraceGamma_family_norm_le u v hu hv huo i j)

end CoefficientBound

end ThreeCopyQutritWerner
