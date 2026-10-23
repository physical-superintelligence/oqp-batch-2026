module

public import ThreeCopyQutritWerner.ThinFirstSiteZeros

@[expose] public section


/-!
# Exact original blocks of a single-output endpoint zero

The diagonal block has weight one half; every other input block has weight
one. All weights are strictly positive and all original block ranks are at
most two. Thus each block is a genuine two-site cut zero unconditionally.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- Exact weighted two-site decomposition for one allowed output coordinate. -/
theorem endpointEnergy_single_output_eq_weighted_cutForm
    (C : Matrix (a × b × c) (a × b × c) ℂ) (k : a)
    (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0) :
    endpointEnergy C = ∑ j, (if j = k then (1 / 2 : ℝ) else 1) *
      cutForm (firstSiteBlock C k j) := by
  have hz : cutForm (0 : Matrix (b × c) (b × c) ℂ) = 0 := by
    simp [cutForm, frobSq, ptraceL, ptraceR, Matrix.trace]
  have hb (i : a) (hi : i ≠ k) (j : a) : firstSiteBlock C i j = 0 := by
    ext r s
    exact hrow i hi r (j, s)
  have ht : ptrace₁ C = firstSiteBlock C k k := by
    rw [ptrace₁_eq_sum_firstSiteBlocks]
    apply Finset.sum_eq_single k
    · intro i _ hi
      exact hb i hi i
    · simp
  have hs : (∑ i, ∑ j, cutForm (firstSiteBlock C i j)) =
      ∑ j, cutForm (firstSiteBlock C k j) := by
    apply Finset.sum_eq_single k
    · intro i _ hi
      simp only [hb i hi, hz, Finset.sum_const_zero]
    · simp
  rw [endpointEnergy_eq_sum_firstSiteBlock_cutForm, ht, hs]
  have hw : (∑ j, (if j = k then (1 / 2 : ℝ) else 1) * cutForm (firstSiteBlock C k j)) =
      (∑ j, cutForm (firstSiteBlock C k j)) - cutForm (firstSiteBlock C k k) / 2 := by
    calc
      _ = ∑ j, (cutForm (firstSiteBlock C k j) -
          if j = k then cutForm (firstSiteBlock C k j) / 2 else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = k <;> simp [hj] <;> ring
      _ = _ := by rw [Finset.sum_sub_distrib]; simp
  exact hw.symm

/-- At a single-output zero all original input blocks are cut zeros, including
the diagonal block. No normalization or endpoint inequality is needed. -/
theorem firstSiteBlock_cutForm_zero_of_single_output_endpoint_zero
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (k : a)
    (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0) (j : a) :
    cutForm (firstSiteBlock C k j) = 0 := by
  rw [endpointEnergy_single_output_eq_weighted_cutForm C k hrow] at hz
  have hn (i : a) : 0 ≤ (if i = k then (1 / 2 : ℝ) else 1) *
      cutForm (firstSiteBlock C k i) :=
    mul_nonneg (by split_ifs <;> norm_num) (firstSiteBlock_cutForm_nonneg C hC k i)
  have hj := congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hn).mp hz) j
  have hw : (if j = k then (1 / 2 : ℝ) else 1) ≠ 0 := by split_ifs <;> norm_num
  exact (mul_eq_zero.mp hj).resolve_left hw

end ThreeCopyQutritWerner
