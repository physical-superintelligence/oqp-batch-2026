module

public import ThreeCopyQutritWerner.SharpDoubleAntisymmetric
public import ThreeCopyQutritWerner.RankTwoSpectralBound

@[expose] public section


/-!
# Sharp rank-two overlap with the double-antisymmetric subspace

The actual Takagi family and the symmetric two-ray projection estimate give
one- and two-weight bounds on every vector in the double-antisymmetric range.
The proved rank-two spectral overlap estimate then gives the sharp factor
one-half for every matrix of rank at most two. No spectral or projection
inequality is assumed as an extra premise.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

section Pairings

variable {L R : Type*} [Fintype L] [Fintype R]

/-- A symmetric rank-one pairing is the square, not norm-square, of the ray pairing. -/
theorem sharpSymmetricRay_pairing (z w : L × R → ℂ) :
    hsInner (sharpSymmetricRay z) (sharpSymmetricRay w) = (braket z w) ^ 2 := by
  simp only [hsInner, sharpSymmetricRay, braket, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_mul]
  ring

theorem sharpSymmetricRay_frobSq (z : L × R → ℂ) :
    frobSq (sharpSymmetricRay z) = vecNormSq z ^ 2 := by
  rw [← zeroReserve_hsInner_self_re, sharpSymmetricRay_pairing, braket_self,
    ← Complex.ofReal_pow, Complex.ofReal_re]

private theorem sharp_hsInner_right_mix
    (X A B : Matrix (L × R) (L × R) ℂ) (c d : ℂ) :
    hsInner X (c • A + d • B) = c * hsInner X A + d * hsInner X B := by
  simp only [hsInner, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem sharp_hsInner_self (X : Matrix (L × R) (L × R) ℂ) :
    hsInner X X = (frobSq X : ℂ) := by
  exact (ofReal_frobSq X).symm

/-- A real antilinear eigenvector has the correct symmetric-ray Hilbert--Schmidt coefficient. -/
theorem sharpSymmetricRay_eigen_pairing
    (X : Matrix (L × R) (L × R) ℂ) (z : L × R → ℂ) (s : ℝ)
    (hz : vecNormSq z = 1)
    (he : X *ᵥ (fun i => conj (z i)) = (s : ℂ) • z) :
    hsInner X (sharpSymmetricRay z) = (s : ℂ) := by
  have hconj : conj (hsInner X (sharpSymmetricRay z)) =
      braket z (X *ᵥ (fun i => conj (z i))) := by
    simp only [hsInner, sharpSymmetricRay, map_sum, map_mul, Complex.conj_conj,
      braket, Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs : braket z ((s : ℂ) • z) = (s : ℂ) * braket z z := by
    simp only [braket, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, hs, braket_self, hz, Complex.ofReal_one, mul_one] at hconj
  have h := congrArg (starRingEnd ℂ) hconj
  simpa only [Complex.conj_conj, Complex.conj_ofReal] using h

/-- An exact projection test with equal norm-square and pairing controls its weight. -/
theorem sharpDoubleAnti_exact_test_le
    (X E : Matrix (L × R) (L × R) ℂ) (hX : sharpDoubleAnti X = X)
    (t : ℝ) (ht : 0 ≤ t) (hE : frobSq E = t) (hpair : hsInner X E = (t : ℂ))
    (hbound : frobSq (sharpDoubleAnti E) ≤ frobSq E / 2) :
    t ≤ frobSq X / 2 := by
  have htrace : (Xᴴ * sharpDoubleAnti E).trace = (t : ℂ) := by
    calc
      (Xᴴ * sharpDoubleAnti E).trace = hsInner X (sharpDoubleAnti E) := by
        simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Complex.star_def]
        exact Finset.sum_comm
      _ = (t : ℂ) := by rw [← sharpDoubleAnti_selfadjoint, hX, hpair]
  have hcs := nuclearTrace_pair_normSq_le X (sharpDoubleAnti E)
  rw [htrace, Complex.normSq_ofReal] at hcs
  rw [hE] at hbound
  have hscaled := mul_le_mul_of_nonneg_left hbound (frobSq_nonneg X)
  by_cases hzero : t = 0
  · rw [hzero]
    exact div_nonneg (frobSq_nonneg X) (by norm_num)
  · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    have hm : t * t ≤ t * (frobSq X / 2) := by nlinarith
    exact le_of_mul_le_mul_left hm hpos

end Pairings

section TakagiWeights

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- The original Takagi coefficient is the exact symmetric-ray overlap. -/
theorem sharpDoubleAnti_takagi_pairing (X : Matrix (L × R) (L × R) ℂ)
    (hX : Xᵀ = X) (i : TakagiPositiveIndex X hX) :
    hsInner X (sharpSymmetricRay (takagiVector X hX i)) = (takagiWeight X hX i : ℂ) := by
  apply sharpSymmetricRay_eigen_pairing X _ _ (takagiVector_normSq X hX i)
  exact symmetricRealification_spectral_eigenvector X hX i.val

/-- Every single squared Takagi weight in the projection range is at most half its norm-square. -/
theorem sharpDoubleAnti_takagi_weight_le (X : Matrix (L × R) (L × R) ℂ)
    (hX : Xᵀ = X) (hQ : sharpDoubleAnti X = X) (i : TakagiPositiveIndex X hX) :
    takagiWeight X hX i ^ 2 ≤ frobSq X / 2 := by
  let z := takagiVector X hX i
  let s := takagiWeight X hX i
  let E := (s : ℂ) • sharpSymmetricRay z + (0 : ℂ) • sharpSymmetricRay z
  have hnorm : frobSq E = s ^ 2 := by
    simp only [E, zero_smul, add_zero, frobSq_smul, sharpSymmetricRay_frobSq,
      z, takagiVector_normSq, one_pow, mul_one, Complex.normSq_ofReal]
    ring
  have hpair : hsInner X E = ((s ^ 2 : ℝ) : ℂ) := by
    rw [sharp_hsInner_right_mix, sharpDoubleAnti_takagi_pairing]
    simp only [zero_mul, add_zero, s, Complex.ofReal_pow, pow_two, Complex.ofReal_mul]
  have hbound : frobSq (sharpDoubleAnti E) ≤ frobSq E / 2 :=
    sharpDoubleAnti_symmetric_pair_bound z z s 0 (takagiWeight_pos X hX i).le le_rfl
  exact sharpDoubleAnti_exact_test_le X E hQ (s ^ 2) (sq_nonneg _) hnorm hpair hbound

/-- Every pair of distinct squared Takagi weights has the same sharp half-norm bound. -/
theorem sharpDoubleAnti_takagi_pair_le (X : Matrix (L × R) (L × R) ℂ)
    (hX : Xᵀ = X) (hQ : sharpDoubleAnti X = X)
    (i j : TakagiPositiveIndex X hX) (hij : i ≠ j) :
    takagiWeight X hX i ^ 2 + takagiWeight X hX j ^ 2 ≤ frobSq X / 2 := by
  let z := takagiVector X hX i
  let w := takagiVector X hX j
  let s := takagiWeight X hX i
  let t := takagiWeight X hX j
  let E := (s : ℂ) • sharpSymmetricRay z + (t : ℂ) • sharpSymmetricRay w
  have hnorm : frobSq E = s ^ 2 + t ^ 2 := by
    rw [zeroReserve_frobSq_real_mix, sharpSymmetricRay_frobSq, sharpSymmetricRay_frobSq,
      sharpSymmetricRay_pairing]
    simp only [z, w, takagiVector_normSq, takagiVector_braket, if_neg hij, one_pow,
      mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0), Complex.zero_re, mul_zero, add_zero]
  have hpair : hsInner X E = ((s ^ 2 + t ^ 2 : ℝ) : ℂ) := by
    rw [sharp_hsInner_right_mix, sharpDoubleAnti_takagi_pairing, sharpDoubleAnti_takagi_pairing]
    simp only [s, t, Complex.ofReal_add, Complex.ofReal_pow, pow_two, Complex.ofReal_mul]
  have hbound : frobSq (sharpDoubleAnti E) ≤ frobSq E / 2 :=
    sharpDoubleAnti_symmetric_pair_bound z w s t
      (takagiWeight_pos X hX i).le (takagiWeight_pos X hX j).le
  exact sharpDoubleAnti_exact_test_le X E hQ (s ^ 2 + t ^ 2)
    (add_nonneg (sq_nonneg _) (sq_nonneg _)) hnorm hpair hbound

/-- Wu--Zou's sharp projection lemma for every matrix of rank at most two,
with the literal two-replica double-antisymmetrizer and no spectral premise. -/
theorem sharpDoubleAnti_rank_two_bound (Y : Matrix (L × R) (L × R) ℂ)
    (hY : Y.rank ≤ 2) : frobSq (sharpDoubleAnti Y) ≤ frobSq Y / 2 := by
  let X := sharpDoubleAnti Y
  have hX : Xᵀ = X := sharpDoubleAnti_transpose Y
  have hQ : sharpDoubleAnti X = X := sharpDoubleAnti_idempotent Y
  have htrace : (Xᴴ * Y).trace = (frobSq X : ℂ) := by
    calc
      (Xᴴ * Y).trace = hsInner X Y := by
        simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Complex.star_def]
        exact Finset.sum_comm
      _ = hsInner (sharpDoubleAnti X) Y := by rw [hQ]
      _ = hsInner X (sharpDoubleAnti Y) := sharpDoubleAnti_selfadjoint X Y
      _ = (frobSq X : ℂ) := sharp_hsInner_self X
  have h := rankTwo_takagi_overlap_le X hX Y hY (frobSq X / 2)
    (div_nonneg (frobSq_nonneg X) (by norm_num))
    (sharpDoubleAnti_takagi_weight_le X hX hQ) (sharpDoubleAnti_takagi_pair_le X hX hQ)
  rw [htrace, Complex.normSq_ofReal] at h
  have hn := frobSq_nonneg X
  change frobSq X ≤ frobSq Y / 2
  by_cases hz : frobSq X = 0
  · rw [hz]
    exact div_nonneg (frobSq_nonneg Y) (by norm_num)
  · have hp : 0 < frobSq X := lt_of_le_of_ne hn (Ne.symm hz)
    have hm : frobSq X * frobSq X ≤ frobSq X * (frobSq Y / 2) := by nlinarith
    exact le_of_mul_le_mul_left hm hp

end TakagiWeights

end ThreeCopyQutritWerner
