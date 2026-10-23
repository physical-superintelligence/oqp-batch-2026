module

public import ThreeCopyQutritWerner.BinaryKroneckerRank
public import ThreeCopyQutritWerner.SkewNormalizedFrame
public import ThreeCopyQutritWerner.RankOne

@[expose] public section


/-!
# The full binary two-site cut kernel

For actual two-qubit matrices the two-copy cut form is exactly the squared
Frobenius norm of the component traceless on both sites. Thus every zero has
a scalar-plus-local Kronecker representation. This supplies the binary-carrier
part of Appendix C.3, but does not assert that every thin qutrit zero has such
a carrier.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- The actual two-qubit cut form is the squared norm of the double-traceless part. -/
theorem binaryCorrelation_frobSq
    (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    frobSq (binaryCorrelation C) = cutForm C := by
  simp [binaryCorrelation, cutForm, frobSq, ptraceL, ptraceR, Matrix.trace,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.div_re, Complex.div_im]
  <;> ring

/-- Vanishing of the actual cut form is equivalent to zero double-traceless part. -/
theorem binaryCut_zero_iff_correlation_zero
    (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    cutForm C = 0 ↔ binaryCorrelation C = 0 := by
  rw [← binaryCorrelation_frobSq]
  constructor
  · exact matrix_eq_zero_of_frobSq_eq_zero _
  · intro h
    rw [h]
    simp [frobSq]

/-- Every actual binary cut zero has its canonical scalar and traceless local parts. -/
theorem binaryCut_zero_kronecker_decomposition
    (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hC : cutForm C = 0) :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A.trace = 0 ∧ B.trace = 0 ∧
      C = binaryKroneckerSum (C.trace / 4) A B := by
  let A : Matrix (Fin 2) (Fin 2) ℂ :=
    (1 / 2 : ℂ) • ptraceL C - (C.trace / 4) • 1
  let B : Matrix (Fin 2) (Fin 2) ℂ :=
    (1 / 2 : ℂ) • ptraceR C - (C.trace / 4) • 1
  have hA : A.trace = 0 := by
    simp [A, ptraceL, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two]
    <;> ring
  have hB : B.trace = 0 := by
    simp [B, ptraceR, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two]
    <;> ring
  have hrec : C = binaryKroneckerSum (C.trace / 4) A B + binaryCorrelation C := by
    ext ⟨i, k⟩ ⟨j, l⟩
    fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
      simp [binaryKroneckerSum, binaryCorrelation, A, B,
        Matrix.kroneckerMap_apply, Matrix.one_apply] <;> ring
  refine ⟨A, B, hA, hB, ?_⟩
  rw [(binaryCut_zero_iff_correlation_zero C).mp hC, add_zero] at hrec
  exact hrec

/-- A trace-zero rank-two normalized binary cut zero is the exact B₂ family form. -/
theorem binaryCut_trace_zero_normal_form
    (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hr : C.rank = 2) (hN : frobSq C = 1) (hC : cutForm C = 0) (ht : C.trace = 0) :
    ∃ U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ, Uᴴ * U = 1 ∧ C = binaryB₂ U := by
  obtain ⟨A, B, hA, hB, hrec⟩ := binaryCut_zero_kronecker_decomposition C hC
  rw [ht, zero_div] at hrec
  apply exists_binaryB₂_of_skew_spin C hr hN
  rw [hrec]
  exact binaryKroneckerSum_zero_scalar_spin A B hA hB

/-- In the nonzero-trace branch one physical binary factor is the identity.
The bound is on the actual matrix rank, with no diagonalizability assumption. -/
theorem binaryCut_nonzero_trace_identity_factor
    (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hr : C.rank ≤ 2) (hC : cutForm C = 0) (ht : C.trace ≠ 0) :
    ∃ T : Matrix (Fin 2) (Fin 2) ℂ,
      C = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T ∨
      C = T ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨A, B, hA, hB, hrec⟩ := binaryCut_zero_kronecker_decomposition C hC
  have hc : C.trace / 4 ≠ 0 := div_ne_zero ht (by norm_num)
  have hzero := binaryKroneckerSum_local_zero_of_rank_le_two
    (C.trace / 4) A B hA hB hc (hrec ▸ hr)
  rcases hzero with ha | hb
  · refine ⟨(C.trace / 4) • 1 + B, Or.inr ?_⟩
    conv_lhs => rw [hrec, ha]
    ext ⟨i, k⟩ ⟨j, l⟩
    fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
      simp [binaryKroneckerSum, Matrix.kroneckerMap_apply, Matrix.one_apply]
  · refine ⟨(C.trace / 4) • 1 + A, Or.inl ?_⟩
    conv_lhs => rw [hrec, hb]
    ext ⟨i, k⟩ ⟨j, l⟩
    fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
      simp [binaryKroneckerSum, Matrix.kroneckerMap_apply, Matrix.one_apply]

end ThreeCopyQutritWerner
