module

public import ThreeCopyQutritWerner.SharpPartialTraceGamma

@[expose] public section


/-!
# Exact weighted summation of the partial-trace coefficients

The nonnegative singular weights are summed only after the actual complex
cross coefficients have been bounded. The quadratic identity retains both
literal partial traces and the trace modulus, without a rank replacement.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

section FinitePairing

variable {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n]

private theorem sharp_hsInner_sum_left (A : ι → Matrix m n ℂ) (B : Matrix m n ℂ) :
    hsInner (∑ i, A i) B = ∑ i, hsInner (A i) B := by
  simp only [hsInner, Matrix.sum_apply, map_sum, Finset.sum_mul]
  calc
    (∑ r, ∑ c, ∑ i, conj (A i r c) * B r c) =
        ∑ r, ∑ i, ∑ c, conj (A i r c) * B r c := by
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ = ∑ i, ∑ r, ∑ c, conj (A i r c) * B r c := Finset.sum_comm

private theorem sharp_hsInner_sum_right (A : Matrix m n ℂ) (B : ι → Matrix m n ℂ) :
    hsInner A (∑ i, B i) = ∑ i, hsInner A (B i) := by
  simp only [hsInner, Matrix.sum_apply, Finset.mul_sum]
  calc
    (∑ r, ∑ c, ∑ i, conj (A r c) * B i r c) =
        ∑ r, ∑ i, ∑ c, conj (A r c) * B i r c := by
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ = ∑ i, ∑ r, ∑ c, conj (A r c) * B i r c := Finset.sum_comm

/-- Exact finite sesquilinear expansion, for arbitrary complex scalar weights. -/
theorem sharp_hsInner_weighted_sum (A : ι → Matrix m n ℂ) (w : ι → ℂ) :
    hsInner (∑ i, w i • A i) (∑ i, w i • A i) =
      ∑ i, ∑ j, conj (w i) * w j * hsInner (A i) (A j) := by
  rw [sharp_hsInner_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [sharp_hsInner_sum_right]
  apply Finset.sum_congr rfl
  intro j _
  exact zeroReserve_hsInner_smul _ _ _ _

end FinitePairing

section PartialTraces

variable {ι L R : Type*} [Fintype ι] [Fintype L] [Fintype R]

/-- The first literal partial trace preserves the same weighted matrix sum. -/
theorem sharp_ptraceL_weighted_sum
    (A : ι → Matrix (L × R) (L × R) ℂ) (w : ι → ℂ) :
    ptraceL (∑ i, w i • A i) = ∑ i, w i • ptraceL (A i) := by
  ext r s
  simp only [ptraceL, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- The second literal partial trace preserves the same weighted matrix sum. -/
theorem sharp_ptraceR_weighted_sum
    (A : ι → Matrix (L × R) (L × R) ℂ) (w : ι → ℂ) :
    ptraceR (∑ i, w i • A i) = ∑ i, w i • ptraceR (A i) := by
  ext r s
  simp only [ptraceR, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- The original quadratic contraction is exactly the double sum of complex gamma coefficients. -/
theorem sharpPartialTraceGamma_weighted_complex
    (u v : ι → L × R → ℂ) (w : ι → ℂ) :
    ptraceInner (∑ i, w i • ketBra (u i) (v i)) (∑ i, w i • ketBra (u i) (v i)) -
      conj ((∑ i, w i • ketBra (u i) (v i)).trace) *
        (∑ i, w i • ketBra (u i) (v i)).trace =
      ∑ i, ∑ j, conj (w i) * w j * sharpPartialTraceGamma (u i) (v i) (u j) (v j) := by
  simp only [ptraceInner, sharp_ptraceL_weighted_sum, sharp_ptraceR_weighted_sum,
    sharp_hsInner_weighted_sum, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
    map_sum, map_mul, Finset.sum_mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold sharpPartialTraceGamma ptraceInner
  ring

/-- Taking real parts yields the exact Frobenius and trace-modulus quadratic identity. -/
theorem sharpPartialTraceGamma_weighted_real
    (u v : ι → L × R → ℂ) (w : ι → ℝ) :
    frobSq (ptraceL (∑ i, (w i : ℂ) • ketBra (u i) (v i))) +
      frobSq (ptraceR (∑ i, (w i : ℂ) • ketBra (u i) (v i))) -
      Complex.normSq (∑ i, (w i : ℂ) • ketBra (u i) (v i)).trace =
      ∑ i, ∑ j, w i * w j * (sharpPartialTraceGamma (u i) (v i) (u j) (v j)).re := by
  have h := congrArg Complex.re (sharpPartialTraceGamma_weighted_complex u v
    (fun i => (w i : ℂ)))
  simpa only [ptraceInner, Complex.sub_re, Complex.add_re, zeroReserve_hsInner_self_re,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.re_sum,
    Complex.conj_ofReal, Complex.mul_re, Complex.mul_im, Complex.ofReal_im,
    zero_mul, mul_zero, add_zero, sub_zero] using h

/-- The gamma bound transfers to every actual nonnegative weighted ray sum. -/
theorem sharpPartialTrace_nonnegative_ray_sum_bound
    [DecidableEq L] [DecidableEq R]
    (u v : ι → L × R → ℂ) (w : ι → ℝ)
    (hu : ∀ i, vecNormSq (u i) = 1) (hv : ∀ i, vecNormSq (v i) = 1)
    (huo : ∀ i j, i ≠ j → braket (u i) (u j) = 0) (hw : ∀ i, 0 ≤ w i) :
    frobSq (ptraceL (∑ i, (w i : ℂ) • ketBra (u i) (v i))) +
      frobSq (ptraceR (∑ i, (w i : ℂ) • ketBra (u i) (v i))) ≤
      (∑ i, w i) ^ 2 +
        Complex.normSq (∑ i, (w i : ℂ) • ketBra (u i) (v i)).trace := by
  have hsum : (∑ i, ∑ j, w i * w j *
      (sharpPartialTraceGamma (u i) (v i) (u j) (v j)).re) ≤ (∑ i, w i) ^ 2 := by
    calc
      (∑ i, ∑ j, w i * w j * (sharpPartialTraceGamma (u i) (v i) (u j) (v j)).re) ≤
          ∑ i, ∑ j, w i * w j := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (sharpPartialTraceGamma_family_re_le u v hu hv huo i j) (mul_nonneg (hw i) (hw j))
      _ = (∑ i, w i) ^ 2 := by rw [pow_two, Finset.sum_mul_sum]
  rw [← sharpPartialTraceGamma_weighted_real u v w] at hsum
  linarith

end PartialTraces

end ThreeCopyQutritWerner
