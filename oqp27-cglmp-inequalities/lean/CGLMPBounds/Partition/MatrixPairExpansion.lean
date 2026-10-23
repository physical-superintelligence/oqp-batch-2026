module

public import CGLMPBounds.Circulation.Core

@[expose] public section


/-! Finite matrix algebra for the D.2 Fourier expansion. The normalized
Hilbert–Schmidt form is expanded against the actual correlations. The
scalar baseline is subtracted before taking a singular kernel limit. -/

namespace CGLMPBounds.Partition
open scoped Matrix
noncomputable section

private lemma tr_complex_smul {r : ℕ} (z : ℂ) (M : Circulation.Mat r) :
    Circulation.tr (z • M) = z * Circulation.tr M := by
  simp [Circulation.tr, Matrix.trace_smul, smul_eq_mul, mul_div_assoc]

private lemma tr_finite_sum {ι : Type*} [Fintype ι] {r : ℕ}
    (M : ι → Circulation.Mat r) :
    Circulation.tr (∑ j, M j) = ∑ j, Circulation.tr (M j) := by
  simp [Circulation.tr, Matrix.trace_sum, Finset.sum_div]

lemma corr_dagger_eq_star {r : ℕ} (V W : Circulation.Mat r) :
    Circulation.corr Vᴴ Wᴴ = star (Circulation.corr V W) := by
  unfold Circulation.corr Circulation.tr
  rw [star_div₀, star_natCast, ← Matrix.trace_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.trace_mul_comm]

lemma hsSq_weighted_sum {ι : Type*} [Fintype ι] {r : ℕ}
    (a : ι → ℂ) (W : ι → Circulation.Mat r) :
    Circulation.hsSq (∑ j, a j • W j) =
      (∑ j, ∑ k, star (a j) * a k * Circulation.corr (W j) (W k)).re := by
  unfold Circulation.hsSq Circulation.reTr
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, tr_finite_sum, tr_complex_smul, Circulation.corr]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma norm_sum_sq_eq_pair_sum {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    ‖∑ j, a j‖ ^ 2 = (∑ j, ∑ k, star (a j) * a k).re := by
  have h : star (∑ j, a j) * (∑ k, a k) = ∑ j, ∑ k, star (a j) * a k := by
    simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hr := congrArg Complex.re h
  simpa only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.ofReal_re] using hr

/-- The complex pair expression has the precise conjugation required by
the quarter-root branch U(t)=exp(-πit/2)V(t)†. No unitary assumption is
needed until the diagonal terms are removed. -/
theorem hsSq_weighted_daggers_sub_scalar {ι : Type*} [Fintype ι] {r : ℕ}
    (a : ι → ℂ) (V : ι → Circulation.Mat r) :
    Circulation.hsSq (∑ j, a j • (V j)ᴴ) - ‖∑ j, a j‖ ^ 2 =
      ∑ j, ∑ k, (star (a j) * a k * (star (Circulation.corr (V j) (V k)) - 1)).re := by
  rw [hsSq_weighted_sum, norm_sum_sq_eq_pair_sum]
  simp only [corr_dagger_eq_star, Complex.re_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [← Complex.sub_re]
  congr 1
  ring

lemma symmetric_zero_diagonal_pair_sum {d : ℕ} (f : Fin d → Fin d → ℝ)
    (hsymm : ∀ j k, f j k = f k j) (hdiag : ∀ j, f j j = 0) :
    (∑ j, ∑ k, f j k) = 2 * ∑ j, ∑ k, if j < k then f j k else 0 := by
  have he (j k : Fin d) : f j k =
      (if j < k then f j k else 0) + (if k < j then f k j else 0) := by
    rcases lt_trichotomy j k with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst k
      simp [hdiag]
    · simp [h, not_lt_of_ge h.le, hsymm]
  have hswap : (∑ j : Fin d, ∑ k : Fin d, if k < j then f k j else 0) =
      ∑ j : Fin d, ∑ k : Fin d, if j < k then f j k else 0 := by
    rw [Finset.sum_comm]
  calc
    _ = ∑ j, ∑ k,
        ((if j < k then f j k else 0) + (if k < j then f k j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      exact he j k
    _ = (∑ j, ∑ k, if j < k then f j k else 0) +
        (∑ j, ∑ k, if k < j then f k j else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hswap]; ring

private lemma corr_swap_local {r : ℕ} (V W : Circulation.Mat r) :
    Circulation.corr W V = star (Circulation.corr V W) := by
  -- The short algebraic proof is the same as Circulation.corr_swap;
  -- using it here avoids importing the unrelated scalar Hodge chain.
  unfold Circulation.corr Circulation.tr
  rw [star_div₀, star_natCast, ← Matrix.trace_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- The diagonal cancels against the scalar baseline and the two ordered
half-squares pair with an exact factor two. -/
theorem hsSq_weighted_unitary_daggers_sub_scalar {d r : ℕ} (hr : 0 < r)
    (a : Fin d → ℂ) (V : Fin d → Circulation.Mat r)
    (hV : ∀ j, (V j)ᴴ * V j = 1) :
    Circulation.hsSq (∑ j, a j • (V j)ᴴ) - ‖∑ j, a j‖ ^ 2 =
      2 * ∑ j : Fin d, ∑ k : Fin d, if j < k then
        (star (a j) * a k * (star (Circulation.corr (V j) (V k)) - 1)).re else 0 := by
  rw [hsSq_weighted_daggers_sub_scalar]
  apply symmetric_zero_diagonal_pair_sum
  · intro j k
    have he : star (a k) * a j * (star (Circulation.corr (V k) (V j)) - 1) =
        star (star (a j) * a k * (star (Circulation.corr (V j) (V k)) - 1)) := by
      rw [corr_swap_local]
      simp only [star_star, star_mul, star_sub, star_one]
      ring
    rw [he]
    simp only [Complex.star_def, Complex.conj_re]
  · intro j
    have he : Circulation.corr (V j) (V j) = 1 := by
      simp [Circulation.corr, Circulation.tr, hV j, Nat.ne_of_gt hr]
    simp [he]

end
end CGLMPBounds.Partition
