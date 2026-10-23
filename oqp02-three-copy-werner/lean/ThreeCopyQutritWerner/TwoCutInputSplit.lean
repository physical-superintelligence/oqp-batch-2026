module

public import ThreeCopyQutritWerner.FirstSiteInputSplit
public import ThreeCopyQutritWerner.TraceEqualityScale

@[expose] public section


/-!
# Two-site input splitting and exact off-plane projection blocks

At a missing output coordinate, the ordinary two-site cut form splits
across the corresponding input coordinate. Unlike the three-site split,
both pieces are nonnegative by already proved results, so zero inheritance
is unconditional. Every nonzero off-plane block is an actual scalar
orthogonal two-plane projection with coefficient given by its own trace.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- The rank-two trace-bound defect on an ordinary square complex matrix. -/
def twoCutTraceDefect {n : Type*} [Fintype n] (B : Matrix n n ℂ) : ℝ :=
  frobSq B - Complex.normSq B.trace / 2

theorem twoCutTraceDefect_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) (hB : B.rank ≤ 2) : 0 ≤ twoCutTraceDefect B := by
  have h := normSq_trace_le_two_mul_of_rank_le_two B hB
  change Complex.normSq B.trace ≤ 2 * frobSq B at h
  unfold twoCutTraceDefect
  linarith

private theorem twoCutTraceDefect_zero {n : Type*} [Fintype n] :
    twoCutTraceDefect (0 : Matrix n n ℂ) = 0 := by
  simp [twoCutTraceDefect, frobSq, Matrix.trace]

variable {a b : Type*} [Fintype a] [Fintype b]

/-- Literal block formula for the original two-site cut form. -/
theorem cutForm_eq_sum_firstSiteBlock_traceDefect
    (C : Matrix (a × b) (a × b) ℂ) :
    cutForm C = (∑ i, ∑ j, twoCutTraceDefect (firstSiteBlock C i j)) -
      twoCutTraceDefect (ptraceL C) / 2 := by
  have hr : frobSq (ptraceR C) =
      ∑ i, ∑ j, Complex.normSq (firstSiteBlock C i j).trace := by
    rfl
  have ht : (ptraceL C).trace = C.trace := by
    simp only [Matrix.trace, Matrix.diag_apply, ptraceL]
    calc
      _ = ∑ i : a, ∑ j : b, C (i, j) (i, j) := Finset.sum_comm
      _ = _ := (Fintype.sum_prod_type (fun p : a × b => C p p)).symm
  simp only [cutForm, twoCutTraceDefect, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← frobSq_eq_sum_firstSiteBlocks, ← hr, ht]
  ring

variable [DecidableEq a] [DecidableEq b]

theorem twoCutInputSplit_ptraceL_of_missing_row
    (C : Matrix (a × b) (a × b) ℂ) (k : a)
    (hrow : ∀ r q, C (k, r) q = 0) :
    ptraceL (firstSiteInputKeep C k) = 0 ∧
      ptraceL (firstSiteInputDrop C k) = ptraceL C := by
  have hk : ptraceL (firstSiteInputKeep C k) = 0 := by
    ext r s
    simp [ptraceL, firstSiteInputKeep, hrow]
  refine ⟨hk, ?_⟩
  have he : ptraceL (firstSiteInputKeep C k) +
      ptraceL (firstSiteInputDrop C k) = ptraceL C := by
    ext r s
    simp only [ptraceL, Matrix.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (congrFun (firstSiteInputKeep_add_drop C k) (i, r)) (i, s)
  simpa only [hk, zero_add] using he

/-- Exact orthogonal input-coordinate splitting of the original cut form. -/
theorem cutForm_firstSiteInputSplit
    (C : Matrix (a × b) (a × b) ℂ) (k : a)
    (hrow : ∀ r q, C (k, r) q = 0) :
    cutForm C = cutForm (firstSiteInputKeep C k) +
      cutForm (firstSiteInputDrop C k) := by
  obtain ⟨hk, hd⟩ := twoCutInputSplit_ptraceL_of_missing_row C k hrow
  have hs : (∑ i, ∑ j, twoCutTraceDefect (firstSiteBlock (firstSiteInputKeep C k) i j)) +
      (∑ i, ∑ j, twoCutTraceDefect (firstSiteBlock (firstSiteInputDrop C k) i j)) =
        ∑ i, ∑ j, twoCutTraceDefect (firstSiteBlock C i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j = k <;>
      simp only [firstSiteBlock_inputKeep, firstSiteBlock_inputDrop, h,
        if_true, if_false, twoCutTraceDefect_zero, zero_add, add_zero]
  simp only [cutForm_eq_sum_firstSiteBlock_traceDefect, hk, hd, twoCutTraceDefect_zero]
  linarith

/-- The off-plane cut form is exactly the sum of original trace defects. -/
theorem cutForm_firstSiteInputKeep_eq_sum
    (C : Matrix (a × b) (a × b) ℂ) (k : a)
    (hrow : ∀ r q, C (k, r) q = 0) :
    cutForm (firstSiteInputKeep C k) =
      ∑ i, twoCutTraceDefect (firstSiteBlock C i k) := by
  rw [cutForm_eq_sum_firstSiteBlock_traceDefect,
    (twoCutInputSplit_ptraceL_of_missing_row C k hrow).1,
    twoCutTraceDefect_zero, zero_div, sub_zero]
  simp [firstSiteBlock_inputKeep, apply_ite, twoCutTraceDefect_zero]

/-- Both restrictions of an original two-site zero are zeros, with no
three-copy endpoint inequality or classification premise. -/
theorem cutForm_firstSiteInputSplit_zero
    (C : Matrix (a × b) (a × b) ℂ) (hC : C.rank ≤ 2)
    (hz : cutForm C = 0) (k : a) (hrow : ∀ r q, C (k, r) q = 0) :
    cutForm (firstSiteInputKeep C k) = 0 ∧
      cutForm (firstSiteInputDrop C k) = 0 := by
  have hk := cutForm_nonneg_of_rank_le_two _ ((firstSiteInputSplit_rank_le C k).1.trans hC)
  have hd := cutForm_nonneg_of_rank_le_two _ ((firstSiteInputSplit_rank_le C k).2.trans hC)
  have he := cutForm_firstSiteInputSplit C k hrow
  constructor <;> linarith

/-- Every original off-plane block saturates the rank-two trace inequality. -/
theorem firstSiteBlock_trace_saturated_of_cutForm_zero
    (C : Matrix (a × b) (a × b) ℂ) (hC : C.rank ≤ 2)
    (hz : cutForm C = 0) (k : a) (hrow : ∀ r q, C (k, r) q = 0) (i : a) :
    Complex.normSq (firstSiteBlock C i k).trace = 2 * frobSq (firstSiteBlock C i k) := by
  have hs := (cutForm_firstSiteInputSplit_zero C hC hz k hrow).1
  rw [cutForm_firstSiteInputKeep_eq_sum C k hrow] at hs
  have hi := congrFun ((Fintype.sum_eq_zero_iff_of_nonneg
    (fun j => twoCutTraceDefect_nonneg _ ((firstSiteBlock_rank_le C j k).trans hC))).mp hs) i
  change frobSq (firstSiteBlock C i k) -
    Complex.normSq (firstSiteBlock C i k).trace / 2 = 0 at hi
  linarith

/-- Every nonzero off-plane block is the exact original scalar projection,
with its own trace coefficient and a constructed orthonormal pair. -/
theorem firstSiteBlock_projection_of_cutForm_zero
    (C : Matrix (a × b) (a × b) ℂ) (hC : C.rank ≤ 2)
    (hz : cutForm C = 0) (k : a) (hrow : ∀ r q, C (k, r) q = 0)
    (i : a) (hne : firstSiteBlock C i k ≠ 0) :
    ∃ e₀ e₁ : b → ℂ, vecNormSq e₀ = 1 ∧ vecNormSq e₁ = 1 ∧ braket e₀ e₁ = 0 ∧
      (firstSiteBlock C i k).trace ≠ 0 ∧
      firstSiteBlock C i k = ((firstSiteBlock C i k).trace / 2) •
        (ketBra e₀ e₀ + ketBra e₁ e₁) :=
  eq_trace_smul_proj_of_trace_bound_saturated _ ((firstSiteBlock_rank_le C i k).trans hC)
    hne (firstSiteBlock_trace_saturated_of_cutForm_zero C hC hz k hrow i)

end ThreeCopyQutritWerner
