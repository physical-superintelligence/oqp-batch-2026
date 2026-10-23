module

public import ThreeCopyQutritWerner.TwoCutZeroEquality

@[expose] public section


/-!
# Nonzero two-site cut zeros have actual rank two

On rank one, the polarized defect and the ordinary rank-one trace bound give
cutForm C at least one quarter of its squared Frobenius norm. This excludes
all nonzero lower-rank cut zeros before the binary classification is invoked.
-/

noncomputable section

namespace ThreeCopyQutritWerner

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- The original rank-one cut inequality is strictly positive away from zero. -/
theorem frobSq_le_four_mul_cutForm_of_rank_le_one
    (C : Matrix (L × R) (L × R) ℂ) (hC : C.rank ≤ 1) :
    frobSq C ≤ 4 * cutForm C := by
  obtain ⟨x, y, he⟩ := exists_eq_ketBra_of_rank_le_one C hC
  have hb : 0 ≤ frobSq C + Complex.normSq C.trace - ptraceNormSq C := by
    rw [he, frobSq_ketBra_vecNormSq, trace_ketBra]
    exact biDefect_nonneg x y
  have ht : Complex.normSq C.trace ≤ frobSq C := by
    simpa only [frobSq, Nat.cast_one, one_mul] using
      normSq_trace_le_mul_of_rank_le C 1 hC
  unfold cutForm ptraceNormSq at *
  linarith

/-- Exact rank two follows from the original nonzero cut-zero hypotheses. -/
theorem rank_two_of_nonzero_cutForm_zero
    (C : Matrix (L × R) (L × R) ℂ) (hC : C.rank ≤ 2)
    (hz : cutForm C = 0) (hne : C ≠ 0) : C.rank = 2 := by
  by_contra hr
  have hsmall : C.rank ≤ 1 := by omega
  have h := frobSq_le_four_mul_cutForm_of_rank_le_one C hsmall
  rw [hz, mul_zero] at h
  exact hne (matrix_eq_zero_of_frobSq_eq_zero C (le_antisymm h (frobSq_nonneg C)))

end ThreeCopyQutritWerner
