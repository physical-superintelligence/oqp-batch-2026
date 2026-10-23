module

public import ThreeCopyQutritWerner.InteriorReduction

@[expose] public section


/-!
# Exact six-term decomposition of the two-site quadratic form

Only the original cut form is used. The six nonnegative weights correspond
to the three orthogonal binary ray pairs; no endpoint inequality or rank
assumption enters the algebraic identity.
-/

noncomputable section

namespace ThreeCopyQutritWerner

variable {L R : Type*} [Fintype L] [Fintype R]

/-- The signed cut form still satisfies the parallelogram identity. -/
theorem cutForm_parallelogram (A B : Matrix (L × R) (L × R) ℂ) :
    cutForm (A + B) + cutForm (A - B) = 2 * cutForm A + 2 * cutForm B := by
  simp only [cutForm, ptraceL_add, ptraceR_add, ptraceL_sub, ptraceR_sub,
    frobSq_add, frobSq_sub, Matrix.trace_add, Matrix.trace_sub,
    normSq_add_conj_mul, normSq_sub_conj_mul]
  ring

/-- Literal binary first-site contraction identity, with all denominators
outside the original unnormalized two-site matrices. -/
theorem cutForm_six_contractions (A B D E : Matrix (L × R) (L × R) ℂ) :
    cutForm A + cutForm B + cutForm D + cutForm E - cutForm (A + E) / 2 =
      cutForm B / 2 + cutForm D / 2 +
        (cutForm ((A - E) + (D - B)) + cutForm ((A - E) - (D - B)) +
          cutForm ((A - E) + Complex.I • (B + D)) +
          cutForm ((A - E) - Complex.I • (B + D))) / 8 := by
  have h₁ := cutForm_parallelogram (A - E) (D - B)
  have h₂ := cutForm_parallelogram (A - E) (Complex.I • (B + D))
  have h₃ := cutForm_parallelogram D B
  have h₄ := cutForm_parallelogram A E
  rw [cutForm_smul, Complex.normSq_I, one_mul] at h₂
  rw [add_comm D B] at h₃
  linarith

end ThreeCopyQutritWerner
