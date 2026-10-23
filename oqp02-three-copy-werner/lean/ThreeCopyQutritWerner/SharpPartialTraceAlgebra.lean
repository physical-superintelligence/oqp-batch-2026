module

public import ThreeCopyQutritWerner.NuclearTraceCompound

@[expose] public section


/-!
# Hilbert--Schmidt bounds for the sharp double-antisymmetric projection

This supplies the finite matrix inequalities in the symmetric two-ray step of
Wu--Zou, arXiv:2608.02647v1, Section 3. All traces and Frobenius quantities are
literal. The full Schmidt-rank-two projection bound and the sharp nuclear
partial-trace theorem are separate obligations; neither is assumed here.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- The fourth-power Hilbert--Schmidt bound, proved by cyclic trace and ordinary Cauchy--Schwarz. -/
theorem sharpPartialTrace_cross_frobSq_sq_le
    {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) :
    frobSq (Aᴴ * B) ^ 2 ≤ frobSq (Aᴴ * A) * frobSq (Bᴴ * B) := by
  have ht : ((A * Aᴴ)ᴴ * (B * Bᴴ)).trace = (frobSq (Aᴴ * B) : ℂ) := by
    calc
      ((A * Aᴴ)ᴴ * (B * Bᴴ)).trace = ((A * (Aᴴ * B)) * Bᴴ).trace := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = (Bᴴ * (A * (Aᴴ * B))).trace := Matrix.trace_mul_comm _ _
      _ = (frobSq (Aᴴ * B) : ℂ) := by
        rw [ofReal_frobSq_eq_trace]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
  have h := nuclearTrace_pair_normSq_le (A * Aᴴ) (B * Bᴴ)
  rw [ht, Complex.normSq_ofReal, ← zeroReserve_frobSq_gram A,
    ← zeroReserve_frobSq_gram B] at h
  nlinarith

/-- Taking the nonnegative square root retains the original two Gram purities. -/
theorem sharpPartialTrace_cross_frobSq_le
    {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) :
    frobSq (Aᴴ * B) ≤
      Real.sqrt (frobSq (Aᴴ * A)) * Real.sqrt (frobSq (Bᴴ * B)) := by
  have h := sharpPartialTrace_cross_frobSq_sq_le A B
  have hA := Real.sq_sqrt (frobSq_nonneg (Aᴴ * A))
  have hB := Real.sq_sqrt (frobSq_nonneg (Bᴴ * B))
  have hn := frobSq_nonneg (Aᴴ * B)
  have hr := mul_nonneg (Real.sqrt_nonneg (frobSq (Aᴴ * A)))
    (Real.sqrt_nonneg (frobSq (Bᴴ * B)))
  have hs : (Real.sqrt (frobSq (Aᴴ * A)) * Real.sqrt (frobSq (Bᴴ * B))) ^ 2 =
      frobSq (Aᴴ * A) * frobSq (Bᴴ * B) := by rw [mul_pow, hA, hB]
  nlinarith

/-- The potentially non-Hermitian cross-square trace has the required sharp absolute bound. -/
theorem sharpPartialTrace_cross_square_trace_le
    {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) :
    ‖((Aᴴ * B) * (Aᴴ * B)).trace‖ ≤
      Real.sqrt (frobSq (Aᴴ * A)) * Real.sqrt (frobSq (Bᴴ * B)) :=
  (nuclearTrace_square_trace_le (Aᴴ * B)).trans (sharpPartialTrace_cross_frobSq_le A B)

/-- The local-swap quadratic expression for a symmetric two-ray truncation is nonnegative. -/
theorem sharpPartialTrace_symmetric_pair_square_bound
    {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (c * Real.sqrt (frobSq (Aᴴ * A)) - d * Real.sqrt (frobSq (Bᴴ * B))) ^ 2 ≤
      c ^ 2 * frobSq (Aᴴ * A) + d ^ 2 * frobSq (Bᴴ * B) +
        2 * c * d * (((Aᴴ * B) * (Aᴴ * B)).trace).re := by
  have hnorm := sharpPartialTrace_cross_square_trace_le A B
  have hre := Complex.re_le_norm (-((Aᴴ * B) * (Aᴴ * B)).trace)
  simp only [Complex.neg_re, norm_neg] at hre
  have hcross : -(Real.sqrt (frobSq (Aᴴ * A)) * Real.sqrt (frobSq (Bᴴ * B))) ≤
      (((Aᴴ * B) * (Aᴴ * B)).trace).re := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hcross
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc) hd)
  have hA := Real.sq_sqrt (frobSq_nonneg (Aᴴ * A))
  have hB := Real.sq_sqrt (frobSq_nonneg (Bᴴ * B))
  have hcA : (c * Real.sqrt (frobSq (Aᴴ * A))) ^ 2 =
      c ^ 2 * frobSq (Aᴴ * A) := by rw [mul_pow, hA]
  have hdB : (d * Real.sqrt (frobSq (Bᴴ * B))) ^ 2 =
      d ^ 2 * frobSq (Bᴴ * B) := by rw [mul_pow, hB]
  nlinarith [hcA, hdB]

end ThreeCopyQutritWerner
