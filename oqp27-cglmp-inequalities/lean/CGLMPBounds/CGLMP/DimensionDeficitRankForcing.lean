module

public import CGLMPBounds.CGLMP.DimensionDeficitConjugation
public import CGLMPBounds.CGLMP.FourierReducingRank

@[expose] public section


/-!
# Projection ranks are rigid below total squared distance two

Supplement Corollary E.2, printed p.21. For two projections the squared
Frobenius distance dominates their rank difference. For two PVMs the sums
of the ranks agree, so a rank discrepancy costs at least two in total.

This is a reusable ingredient of the rank-forcing corollary. Its application
to a Bell deficit still requires the full stability theorem A.2; no such
bound is assumed to have been established here.
-/

open Matrix
namespace CGLMPBounds
noncomputable section
variable {n : ℕ}

lemma re_trace_eq_rank_of_idempotent
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : P * P = P) :
    (Matrix.trace P).re = (P.rank : ℝ) := by
  rw [trace_eq_rank_of_idempotent P hP]
  simp

lemma deficitHSSq_projection_self {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.IsHermitian) (hP2 : P * P = P) :
    deficitHSSq P = (P.rank : ℝ) := by
  rw [deficitHSSq, hP.eq, hP2, re_trace_eq_rank_of_idempotent P hP2]

lemma projection_overlap_le_rank_right {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.IsHermitian) (hP2 : P * P = P)
    (hQ : Q.IsHermitian) (hQ2 : Q * Q = Q) :
    (Matrix.trace (P * Q)).re ≤ (Q.rank : ℝ) := by
  have hR : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hP
  have hR2 : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP2]
    abel
  have hnonneg := deficitHSSq_nonneg ((1 - P) * Q)
  rw [deficitHSSq_projection_right hQ hQ2, hR.eq, hR2,
    Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    re_trace_eq_rank_of_idempotent Q hQ2] at hnonneg
  linarith

/-- A difference in projection ranks costs at least that much squared
Frobenius distance. No commutation or rank positivity is needed. -/
theorem projection_rank_difference_le_deficitHSSq
    {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.IsHermitian) (hP2 : P * P = P)
    (hQ : Q.IsHermitian) (hQ2 : Q * Q = Q) :
    |(P.rank : ℝ) - (Q.rank : ℝ)| ≤ deficitHSSq (P - Q) := by
  have hright := projection_overlap_le_rank_right hP hP2 hQ hQ2
  have hleft := projection_overlap_le_rank_right hQ hQ2 hP hP2
  rw [Matrix.trace_mul_comm Q P] at hleft
  rw [deficitHSSq_sub, deficitHSSq_projection_self hP hP2,
    deficitHSSq_projection_self hQ hQ2, hP.eq]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable {α : Type*} [Fintype α]

/-- The ordinary matrix ranks of a PVM sum to the ambient dimension. -/
theorem IsPVM.sum_rank {P : α → Matrix (Fin n) (Fin n) ℂ}
    (hP : IsPVM P) : ∑ a, (P a).rank = n := by
  have ht : (∑ a, ((P a).rank : ℂ)) = (n : ℂ) := by
    simp_rw [← trace_eq_rank_of_idempotent _ (hP.mul_self _)]
    rw [← Matrix.trace_sum, hP.sum_eq_one, Matrix.trace_one]
    simp
  exact_mod_cast ht

/-- A coordinate of a zero-sum vector accounts for at most half its total
absolute mass. This avoids making a nonzero-rank assumption. -/
theorem twice_abs_le_sum_abs_of_sum_eq_zero (r : α → ℝ)
    (hr : ∑ a, r a = 0) (a : α) :
    2 * |r a| ≤ ∑ b, |r b| := by
  classical
  have hsplit := Finset.sum_erase_add Finset.univ r (Finset.mem_univ a)
  have herase : ∑ b ∈ Finset.univ.erase a, r b = -r a := by
    rw [hr] at hsplit
    linarith
  have htri := Finset.abs_sum_le_sum_abs r (Finset.univ.erase a)
  rw [herase, abs_neg] at htri
  have hsplitAbs := Finset.sum_erase_add Finset.univ (fun b => |r b|)
    (Finset.mem_univ a)
  linarith

/-- Two natural rank patterns of the same total cannot differ by total
absolute mass strictly less than two. -/
theorem nat_patterns_eq_of_sum_abs_sub_lt_two (p q : α → ℕ)
    (hsum : ∑ a, p a = ∑ a, q a)
    (hdist : ∑ a, |(p a : ℝ) - (q a : ℝ)| < 2) : ∀ a, p a = q a := by
  have hreal : ∑ a, (p a : ℝ) = ∑ a, (q a : ℝ) := by exact_mod_cast hsum
  have hzero : ∑ a, ((p a : ℝ) - (q a : ℝ)) = 0 := by
    rw [Finset.sum_sub_distrib, hreal, sub_self]
  intro a
  have htwo := twice_abs_le_sum_abs_of_sum_eq_zero
    (fun a => (p a : ℝ) - (q a : ℝ)) hzero a
  have habs : |(p a : ℝ) - (q a : ℝ)| < 1 := by linarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  have hp : p a < q a + 1 := by
    have : (p a : ℝ) < ((q a + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hq : q a < p a + 1 := by
    have : (q a : ℝ) < ((p a + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  omega

/-- The source's total-rank discrepancy threshold for actual PVMs. -/
theorem pvm_ranks_eq_of_total_deficitHSSq_lt_two
    {P Q : α → Matrix (Fin n) (Fin n) ℂ}
    (hP : IsPVM P) (hQ : IsPVM Q)
    (hdist : ∑ a, deficitHSSq (P a - Q a) < 2) :
    ∀ a, (P a).rank = (Q a).rank := by
  apply nat_patterns_eq_of_sum_abs_sub_lt_two
  · rw [hP.sum_rank, hQ.sum_rank]
  · apply lt_of_le_of_lt _ hdist
    exact Finset.sum_le_sum (fun a _ => projection_rank_difference_le_deficitHSSq
      (hP.isHermitian a) (hP.mul_self a) (hQ.isHermitian a) (hQ.mul_self a))

/-- Every outcome has rank `k` if a PVM is within total squared distance two
of an actual PVM all of whose outcomes have rank `k`. -/
theorem pvm_equal_rank_of_close_equal_rank_reference
    {P Q : α → Matrix (Fin n) (Fin n) ℂ}
    (hP : IsPVM P) (hQ : IsPVM Q) (k : ℕ)
    (hQrank : ∀ a, (Q a).rank = k)
    (hdist : ∑ a, deficitHSSq (P a - Q a) < 2) :
    ∀ a, (P a).rank = k := by
  intro a
  exact (pvm_ranks_eq_of_total_deficitHSSq_lt_two hP hQ hdist a).trans (hQrank a)

end
end CGLMPBounds
