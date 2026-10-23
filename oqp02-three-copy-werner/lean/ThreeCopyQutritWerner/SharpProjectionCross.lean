module

public import ThreeCopyQutritWerner.SharpRankTwoProjection

@[expose] public section


/-!
# The off-diagonal quarter bound for the double-antisymmetrizer

A unit complex phase makes the projected cross pairing real and nonnegative.
The rank-two projection estimate and Hilbert--Schmidt Cauchy--Schwarz then give
the sharp quarter bound on crossed tensor rays. This is the off-diagonal step
of Wu--Zou Section 4, with literal coefficient matrices throughout.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- A unit scalar rotates an arbitrary complex number to its nonnegative norm. -/
theorem sharp_exists_phase (z : ℂ) :
    ∃ p : ℂ, Complex.normSq p = 1 ∧ p * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · subst z
    exact ⟨1, by simp, by simp⟩
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hc : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
    · rw [Complex.normSq_div, Complex.normSq_conj, Complex.normSq_ofReal,
        Complex.normSq_eq_norm_sq, pow_two]
      exact div_self (mul_ne_zero hn hn)
    · rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      field_simp [hc] <;> ring

section TensorRays

variable {n : Type*} [Fintype n]

/-- The ordinary coefficient tensor u⊗v, with no conjugation on the second ray. -/
def sharpTensorRay (u v : n → ℂ) : Matrix n n ℂ := fun i j => u i * v j

/-- The literal tensor product preserves the product of the two Hermitian pairings. -/
theorem sharpTensorRay_pairing (u v s t : n → ℂ) :
    hsInner (sharpTensorRay u v) (sharpTensorRay s t) = braket u s * braket v t := by
  simp only [hsInner, sharpTensorRay, braket, Finset.sum_mul_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sharpTensorRay_frobSq (u v : n → ℂ) :
    frobSq (sharpTensorRay u v) = vecNormSq u * vecNormSq v := by
  simp only [frobSq, sharpTensorRay, vecNormSq, Complex.normSq_mul, Finset.sum_mul_sum]

/-- Any two coefficient tensor rays factor through the literal two-column space. -/
theorem sharpTensorRay_mix_rank_le_two (u v s t : n → ℂ) (p : ℂ) :
    (sharpTensorRay u v + p • sharpTensorRay s t).rank ≤ 2 := by
  apply (rank_le_iff_exists_mul _ 2).mpr
  refine ⟨Matrix.of (fun i k => ![u i, s i] k),
    Matrix.of (fun k j => ![v j, p * t j] k), ?_⟩
  ext i j
  simp only [sharpTensorRay, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- Right scalar multiplication is linear for the original finite pairing. -/
theorem sharp_hsInner_smul_right (A B : Matrix n n ℂ) (p : ℂ) :
    hsInner A (p • B) = p * hsInner A B := by
  simpa only [one_smul, map_one, one_mul] using zeroReserve_hsInner_smul A B 1 p

end TensorRays

section QuarterBound

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- A projection cross pairing is unchanged when projecting the first argument too. -/
theorem sharpDoubleAnti_pairing_projected (A B : Matrix (L × R) (L × R) ℂ) :
    hsInner A (sharpDoubleAnti B) = hsInner (sharpDoubleAnti A) (sharpDoubleAnti B) := by
  rw [sharpDoubleAnti_selfadjoint, sharpDoubleAnti_idempotent]

/-- The exact quarter bound on crossed coefficient tensor rays. Only their
unit norms and orthogonality in the first tensor factor are required. -/
theorem sharpDoubleAnti_cross_norm_le_quarter
    (u v s t : L × R → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1)
    (hs : vecNormSq s = 1) (ht : vecNormSq t = 1) (hus : braket u s = 0) :
    ‖hsInner (sharpTensorRay u v) (sharpDoubleAnti (sharpTensorRay s t))‖ ≤ 1 / 4 := by
  let A := sharpTensorRay u v
  let B := sharpTensorRay s t
  let a := frobSq (sharpDoubleAnti A)
  let b := frobSq (sharpDoubleAnti B)
  let z := hsInner (sharpDoubleAnti A) (sharpDoubleAnti B)
  have hA : frobSq A = 1 := by simp only [A, sharpTensorRay_frobSq, hu, hv, one_mul]
  have hB : frobSq B = 1 := by simp only [B, sharpTensorRay_frobSq, hs, ht, one_mul]
  have hAB : hsInner A B = 0 := by rw [sharpTensorRay_pairing, hus, zero_mul]
  obtain ⟨p, hp, hpz⟩ := sharp_exists_phase z
  have hnorm : frobSq (A + p • B) = 2 := by
    rw [frobSq_add, frobSq_smul, hA, hB, hp, sharp_hsInner_smul_right, hAB]
    norm_num
  have hphase : (p * z).re = ‖z‖ := by rw [hpz, Complex.ofReal_re]
  have hsum : a + b + 2 * ‖z‖ ≤ 1 := by
    have h := sharpDoubleAnti_rank_two_bound (A + p • B)
      (sharpTensorRay_mix_rank_le_two u v s t p)
    rw [hnorm, sharpDoubleAnti_add, sharpDoubleAnti_smul, frobSq_add, frobSq_smul,
      hp, one_mul, sharp_hsInner_smul_right] at h
    change a + b + 2 * (p * z).re ≤ 2 / 2 at h
    rw [hphase] at h
    norm_num at h
    exact h
  have hcs : ‖z‖ ^ 2 ≤ a * b := by
    have h := nuclearTrace_pair_normSq_le (sharpDoubleAnti A) (sharpDoubleAnti B)
    have htrace : ((sharpDoubleAnti A)ᴴ * sharpDoubleAnti B).trace =
        hsInner (sharpDoubleAnti A) (sharpDoubleAnti B) := by
      simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Complex.star_def]
      exact Finset.sum_comm
    rw [htrace, Complex.normSq_eq_norm_sq] at h
    exact h
  have ha : 0 ≤ a := frobSq_nonneg _
  have hb : 0 ≤ b := frobSq_nonneg _
  have hcross : 2 * ‖z‖ ≤ a + b := by
    apply (sq_le_sq₀ (by positivity) (add_nonneg ha hb)).mp
    nlinarith [sq_nonneg (a - b)]
  rw [sharpDoubleAnti_pairing_projected]
  change ‖z‖ ≤ 1 / 4
  linarith

end QuarterBound

end ThreeCopyQutritWerner
