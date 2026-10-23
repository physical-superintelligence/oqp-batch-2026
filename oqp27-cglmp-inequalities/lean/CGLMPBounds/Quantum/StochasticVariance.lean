module

public import Mathlib

@[expose] public section


/-! Exact weighted-variance identities for the stochastic transition matrix
between two orthonormal bases. No spectral-gap conclusion is assumed here. -/

namespace CGLMPBounds
noncomputable section
open Matrix
variable {α β : Type*} [Fintype α] [Fintype β]

lemma weighted_pair_sq (w x : α → ℝ) (hw : ∑ a, w a = 1) :
    (∑ a, ∑ c, w a * w c * (x a - x c) ^ 2) =
      2 * ((∑ a, w a * x a ^ 2) - (∑ a, w a * x a) ^ 2) := by
  have he (a c : α) : w a * w c * (x a - x c) ^ 2 =
      (w a * x a ^ 2) * w c + w a * (w c * x c ^ 2) -
        2 * (w a * x a) * (w c * x c) := by ring
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hw, mul_one, one_mul]
  ring

lemma weighted_pair_normSq (w : α → ℝ) (x : α → ℂ) (hw : ∑ a, w a = 1) :
    (∑ a, ∑ c, w a * w c * Complex.normSq (x a - x c)) =
      2 * ((∑ a, w a * Complex.normSq (x a)) - Complex.normSq (∑ a, (w a : ℂ) * x a)) := by
  have hN (z : ℂ) : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
    simp only [Complex.normSq_apply, pow_two]
  simp only [hN, Complex.sub_re, Complex.sub_im, Complex.re_sum, Complex.im_sum,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, mul_add, Finset.sum_add_distrib]
  rw [weighted_pair_sq w (fun a => (x a).re) hw,
    weighted_pair_sq w (fun a => (x a).im) hw]
  ring

lemma bistochastic_pair_normSq (w : α → β → ℝ) (x : α → ℂ)
    (hrow : ∀ a, ∑ b, w a b = 1) (hcol : ∀ b, ∑ a, w a b = 1) :
    (∑ b, ∑ a, ∑ c, w a b * w c b * Complex.normSq (x a - x c)) =
      2 * (∑ a, Complex.normSq (x a)) -
        2 * ∑ b, Complex.normSq (∑ a, (w a b : ℂ) * x a) := by
  simp_rw [weighted_pair_normSq _ x (hcol _), mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_mul, hrow, one_mul]

lemma re_trace_gram_eq_sum_normSq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℂ) :
    (Matrix.trace (Xᴴ * X)).re = ∑ i, ∑ k, Complex.normSq (X i k) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]

lemma unitary_weight_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (a : ι) : ∑ b, Complex.normSq ((U : Matrix ι ι ℂ) a b) = 1 := by
  have h := congrArg (fun M : Matrix ι ι ℂ => (M a a).re) U.property.2
  simpa only [Matrix.mul_apply, Matrix.star_apply, Complex.re_sum,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Matrix.one_apply_eq,
    Complex.one_re] using h

lemma unitary_weight_col_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (b : ι) : ∑ a, Complex.normSq ((U : Matrix ι ι ℂ) a b) = 1 := by
  have h := congrArg (fun M : Matrix ι ι ℂ => (M b b).re) U.property.1
  have hsq (z : ℂ) : (star z * z).re = Complex.normSq z := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]
  simpa only [Matrix.mul_apply, Matrix.star_apply, Complex.re_sum,
    hsq, Matrix.one_apply_eq, Complex.one_re] using h

/-- The exact Dirichlet energy turns a mean-zero squared-norm contraction
into a scalar gap. This is a generic algebraic bridge; actual spectral
contraction of the Fourier transition remains a separate theorem. -/
lemma stochastic_dirichlet_gap (w : α → α → ℝ) (x : α → ℂ) (γ : ℝ)
    (hrow : ∀ a, ∑ b, w a b = 1) (hcol : ∀ b, ∑ a, w a b = 1)
    (hcontract : (∑ b, Complex.normSq (∑ a, (w a b : ℂ) * x a)) ≤
      (1 - γ) * ∑ a, Complex.normSq (x a)) :
    2 * γ * (∑ a, Complex.normSq (x a)) ≤
      ∑ b, ∑ a, ∑ c, w a b * w c b * Complex.normSq (x a - x c) := by
  rw [bistochastic_pair_normSq w x hrow hcol]
  nlinarith

end
end CGLMPBounds
