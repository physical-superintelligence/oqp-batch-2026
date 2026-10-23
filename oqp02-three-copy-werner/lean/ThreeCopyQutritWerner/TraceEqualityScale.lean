module

public import ThreeCopyQutritWerner.EndpointZeroNormalization
public import ThreeCopyQutritWerner.InteriorReduction

@[expose] public section


/-!
# Unnormalized equality in the rank-two trace bound

The already proved normalized trace equality theorem is applied to the
actual nonzero matrix after a constructed scalar normalization. Restoring
its scale gives the original matrix as its own trace divided by two times
an orthogonal two-plane projection. No normality or positivity is assumed.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- A nonzero rank-at-most-two trace-bound equality has rank exactly two. -/
theorem rank_two_of_trace_bound_saturated {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (hC : C.rank ≤ 2) (hne : C ≠ 0)
    (hT : Complex.normSq C.trace = 2 * frobSq C) : C.rank = 2 := by
  have hpos : 0 < frobSq C := by
    have hn := frobSq_nonneg C
    by_contra h
    exact hne (matrix_eq_zero_of_frobSq_eq_zero C (le_antisymm (not_lt.mp h) hn))
  by_contra htwo
  have hr : C.rank ≤ 1 := by omega
  have h : Complex.normSq C.trace ≤ frobSq C := by
    simpa only [Nat.cast_one, one_mul, frobSq] using
      normSq_trace_le_mul_of_rank_le C 1 hr
  linarith

/-- Exact equality classification at arbitrary nonzero Frobenius norm.
The coefficient is the original trace, so the phase and scale are retained. -/
theorem eq_trace_smul_proj_of_trace_bound_saturated
    {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (hC : C.rank ≤ 2) (hne : C ≠ 0)
    (hT : Complex.normSq C.trace = 2 * frobSq C) :
    ∃ e₀ e₁ : n → ℂ, vecNormSq e₀ = 1 ∧ vecNormSq e₁ = 1 ∧
      braket e₀ e₁ = 0 ∧ C.trace ≠ 0 ∧
      C = (C.trace / 2) • (ketBra e₀ e₀ + ketBra e₁ e₁) := by
  obtain ⟨a, ha, hN⟩ := exists_frobSq_normalizing_scalar C hne
  have hr : (a • C).rank ≤ 2 := by
    rwa [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero ha)]
  have ht : Complex.normSq (a • C).trace = 2 := by
    rw [Matrix.trace_smul, smul_eq_mul, Complex.normSq_mul, hT]
    have hn := hN
    rw [frobSq_smul] at hn
    nlinarith
  obtain ⟨e₀, e₁, z, h₀, h₁, h01, hz, he⟩ :=
    eq_smul_proj_of_normSq_trace (a • C) hr hN ht
  let w := a⁻¹ * z
  have hc : C = w • (ketBra e₀ e₀ + ketBra e₁ e₁) := by
    calc
      C = a⁻¹ • (a • C) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = _ := by rw [he, smul_smul]
  have hz0 : z ≠ 0 := by
    intro h
    simp only [h, Complex.normSq_zero] at hz
    norm_num at hz
  have hw : w ≠ 0 := mul_ne_zero (inv_ne_zero ha) hz0
  have htr : C.trace = 2 * w := by
    rw [hc, Matrix.trace_smul, Matrix.trace_add, trace_ketBra, trace_ketBra,
      braket_self, braket_self, h₀, h₁, Complex.ofReal_one]
    change w * (1 + 1) = 2 * w
    ring
  refine ⟨e₀, e₁, h₀, h₁, h01, ?_, ?_⟩
  · rw [htr]
    exact mul_ne_zero (by norm_num) hw
  · have hwtrace : C.trace / 2 = w := by rw [htr]; ring
    rw [hwtrace]
    exact hc

end ThreeCopyQutritWerner
