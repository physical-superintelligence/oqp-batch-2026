module

public import ThreeCopyQutritWerner.TwoCutColumnProjection
public import ThreeCopyQutritWerner.TwoCutZeroPlanes

@[expose] public section


/-!
# Trace equality at a single output coordinate

With exactly one allowed first-site output coordinate, the literal cut form
is the sum of the input-block trace defects, with half weight on the diagonal
block. Rank-at-most-two zero energy therefore saturates every original block's
trace inequality, without a three-site endpoint assumption.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

variable {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a] [DecidableEq d]

/-- Exact single-output-coordinate cut form, retaining the actual diagonal weight. -/
theorem cutForm_single_output_coordinate
    (C : Matrix (a × d) (a × d) ℂ) (k : a)
    (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0) :
    cutForm C = (∑ j, twoCutTraceDefect (firstSiteBlock C k j)) -
      twoCutTraceDefect (firstSiteBlock C k k) / 2 := by
  have hblock (i j : a) : firstSiteBlock C i j =
      if i = k then firstSiteBlock C k j else 0 := by
    by_cases hi : i = k
    · subst i
      simp
    · ext r s
      simp [firstSiteBlock, hi, hrow i hi]
  have hp : ptraceL C = firstSiteBlock C k k := by
    ext r s
    change (∑ i, C (i, r) (i, s)) = C (k, r) (k, s)
    apply Finset.sum_eq_single k
    · intro i _ hi
      exact hrow i hi r (i, s)
    · simp
  have hzero : twoCutTraceDefect (0 : Matrix d d ℂ) = 0 := by
    simp [twoCutTraceDefect, frobSq, Matrix.trace]
  rw [cutForm_eq_sum_firstSiteBlock_traceDefect, hp]
  congr 1
  apply Finset.sum_eq_single k
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [hblock, if_neg hi, hzero]
  · simp

/-- Every original input block at a single-output cut zero saturates the
rank-two trace bound; the diagonal block's positive half weight is sufficient. -/
theorem firstSiteBlock_trace_saturated_of_single_output
    (C : Matrix (a × d) (a × d) ℂ) (hC : C.rank ≤ 2) (hz : cutForm C = 0)
    (k : a) (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0) :
    ∀ j, Complex.normSq (firstSiteBlock C k j).trace =
      2 * frobSq (firstSiteBlock C k j) := by
  have he := cutForm_single_output_coordinate C k hrow
  have hn (j : a) : 0 ≤ twoCutTraceDefect (firstSiteBlock C k j) :=
    twoCutTraceDefect_nonneg _ ((firstSiteBlock_rank_le C k j).trans hC)
  have hle : twoCutTraceDefect (firstSiteBlock C k k) ≤
      ∑ j, twoCutTraceDefect (firstSiteBlock C k j) :=
    Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ k)
  have hs : (∑ j, twoCutTraceDefect (firstSiteBlock C k j)) = 0 := by
    have hk := hn k
    linarith
  intro j
  have hj : twoCutTraceDefect (firstSiteBlock C k j) = 0 :=
    congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hn).mp hs) j
  unfold twoCutTraceDefect at hj
  linarith

/-- Adjointing a physical block swaps its two original site indices. -/
theorem firstSiteBlock_conjTranspose
    (C : Matrix (a × d) (a × d) ℂ) (i j : a) :
    firstSiteBlock Cᴴ i j = (firstSiteBlock C j i)ᴴ := by
  ext r s
  rfl

end ThreeCopyQutritWerner
