module

public import Mathlib

@[expose] public section


/-!
# Bessel's inequality for finite orthogonal families

Supplement, Appendix F.4, proof of Theorem F.3: "At fixed `y, b`, the nonzero vectors
`v^y_{cb} / √(r^y_{cb})` are orthonormal in `c`. Bessel's inequality and its counterpart in `a`
give (F.11)." This file proves Bessel's inequality in the form used there, for a finite orthogonal
family that may contain zero vectors (their terms are `0/0 = 0`), together with the squared
Cauchy–Schwarz inequality.

* `norm_inner_sq_le` : `|⟨x, y⟩|² ≤ ‖x‖² ‖y‖²`;
* `bessel_orthogonal` : `Σ_i |⟨e_i, x⟩|² / ‖e_i‖² ≤ ‖x‖²` for pairwise orthogonal `e_i`.
-/

namespace CGLMPBounds

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Squared Cauchy–Schwarz inequality. -/
theorem norm_inner_sq_le (x y : E) : ‖inner ℂ x y‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have h := mul_self_le_mul_self (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) x y)
  nlinarith [h]

/-- One term of the projection: `conj(⟨e, x⟩/⟨e, e⟩) ⟨e, x⟩ = |⟨e, x⟩|² / ‖e‖²`. -/
theorem conj_coeff_mul_inner (e x : E) :
    (starRingEnd ℂ) (inner ℂ e x / inner ℂ e e) * inner ℂ e x
      = ((‖inner ℂ e x‖ ^ 2 / ‖e‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_div₀, inner_self_conj, div_mul_eq_mul_div, Complex.conj_mul',
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_pow]

/-- **Bessel's inequality** for a finite orthogonal family `e` (zero vectors allowed):
`Σ_i |⟨e_i, x⟩|² / ‖e_i‖² ≤ ‖x‖²`. -/
theorem bessel_orthogonal {ι : Type*} [Fintype ι] (e : ι → E)
    (he : ∀ i j, i ≠ j → inner ℂ (e i) (e j) = 0) (x : E) :
    ∑ i, ‖inner ℂ (e i) x‖ ^ 2 / ‖e i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  obtain ⟨y, hy⟩ : ∃ y : E, y = ∑ i, (inner ℂ (e i) x / inner ℂ (e i) (e i)) • e i := ⟨_, rfl⟩
  have hey : ∀ j, inner ℂ (e j) y
      = inner ℂ (e j) x / inner ℂ (e j) (e j) * inner ℂ (e j) (e j) := by
    intro j
    rw [hy, inner_sum, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [inner_smul_right]
    · intro i _ hij
      rw [inner_smul_right, he j i (fun h => hij h.symm), mul_zero]
  have hex : ∀ j, inner ℂ (e j) (x - y) = 0 := by
    intro j
    by_cases h : e j = 0
    · rw [h, inner_zero_left]
    · have hn : inner ℂ (e j) (e j) ≠ 0 := inner_self_ne_zero.mpr h
      rw [inner_sub_right, hey j, div_mul_cancel₀ _ hn, sub_self]
  have hyx : inner ℂ y (x - y) = 0 := by
    have h : inner ℂ (∑ i, (inner ℂ (e i) x / inner ℂ (e i) (e i)) • e i) (x - y) = 0 := by
      rw [sum_inner]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [inner_smul_left, hex i, mul_zero]
    rwa [← hy] at h
  have hpy : ‖x‖ * ‖x‖ = ‖y‖ * ‖y‖ + ‖x - y‖ * ‖x - y‖ := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) y (x - y) hyx
    have e1 : y + (x - y) = x := by abel
    rwa [e1] at h
  have hyy : inner ℂ y y = inner ℂ y x := by
    have h : inner ℂ y x = inner ℂ y y + inner ℂ y (x - y) := by
      rw [inner_sub_right]
      ring
    rw [h, hyx, add_zero]
  have hS : inner ℂ y x = ((∑ i, ‖inner ℂ (e i) x‖ ^ 2 / ‖e i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hy, sum_inner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_smul_left, conj_coeff_mul_inner]
  have hnorm : ‖y‖ ^ 2 = ∑ i, ‖inner ℂ (e i) x‖ ^ 2 / ‖e i‖ ^ 2 := by
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) y
    rw [hyy, hS, RCLike.re_to_complex, Complex.ofReal_re] at h
    exact h.symm
  rw [← hnorm]
  nlinarith [hpy, mul_self_nonneg ‖x - y‖]

end

end CGLMPBounds
