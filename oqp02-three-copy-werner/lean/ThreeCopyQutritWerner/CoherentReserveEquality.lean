module

public import ThreeCopyQutritWerner.CoherentReserveBound

@[expose] public section


/-!
# Equality propagation around the actual coherent pencil

An exact vanishing four-phase average of nonnegative reserves forces every
unit phase to have zero reserve. The conclusion concerns the same two source
columns throughout; no phase-dependent factorization is introduced.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- An exact vanishing average propagates to every unit phase of the actual
coherent two-column source. -/
theorem coherentPositiveSource_reserve_zero_of_average
    (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c))
    (havg : zeroReserve (X * Xᴴ + Y * Yᴴ) + 2 * zeroReserve (X * Yᴴ) = 0)
    (z : ℂ) (hz : Complex.normSq z = 1) :
    zeroReserve (coherentPositiveSource X Y z) = 0 := by
  have hYY : (z • Y) * (z • Y)ᴴ = Y * Yᴴ := by
    simp only [Matrix.conjTranspose_smul, Complex.star_def, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ← Complex.normSq_eq_conj_mul_self, hz, Complex.ofReal_one, one_smul]
  have hXY : X * (z • Y)ᴴ = conj z • (X * Yᴴ) := by
    simp only [Matrix.conjTranspose_smul, Complex.star_def, Matrix.mul_smul]
  have hsum := coherentPositiveSource_four_phase X (z • Y)
  rw [hYY, hXY, zeroReserve_smul, Complex.normSq_conj, hz, one_mul] at hsum
  have h1 := coherentPositiveSource_reserve_nonneg X (z • Y) 1 hn
  have h2 := coherentPositiveSource_reserve_nonneg X (z • Y) (-1) hn
  have h3 := coherentPositiveSource_reserve_nonneg X (z • Y) Complex.I hn
  have h4 := coherentPositiveSource_reserve_nonneg X (z • Y) (-Complex.I) hn
  have he : coherentPositiveSource X (z • Y) 1 = coherentPositiveSource X Y z := by
    simp only [coherentPositiveSource, one_smul]
  rw [he] at hsum h1
  linarith

/-- If the two endpoint reserves agree, saturation of the geometric-mean
coherent inequality is exactly a vanishing four-phase average. -/
theorem coherentPositiveSource_average_zero_of_saturation
    (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c))
    (heq : zeroReserve (X * Xᴴ) = zeroReserve (Y * Yᴴ))
    (hsat : coherentReserveMixed (X * Xᴴ) (Y * Yᴴ) + zeroReserve (X * Yᴴ) =
      -Real.sqrt (zeroReserve (X * Xᴴ) * zeroReserve (Y * Yᴴ))) :
    zeroReserve (X * Xᴴ + Y * Yᴴ) + 2 * zeroReserve (X * Yᴴ) = 0 := by
  have hx : 0 ≤ zeroReserve (X * Xᴴ) := by
    simpa [coherentPositiveSource] using coherentPositiveSource_reserve_nonneg X 0 0 hn
  have hs : Real.sqrt (zeroReserve (X * Xᴴ) * zeroReserve (Y * Yᴴ)) =
      zeroReserve (X * Xᴴ) := by
    rw [← heq, ← pow_two, Real.sqrt_sq hx]
  rw [hs] at hsat
  have hm := zeroReserve_real_mix (X * Xᴴ) (Y * Yᴴ) 1 1
  simp only [Complex.ofReal_one, one_smul, one_pow, one_mul] at hm
  linarith

/-- Every unit phase saturates the actual positive-source reserve under the
exact equal-reserve and coherent-bound equality conditions. -/
theorem coherentPositiveSource_reserve_zero_of_saturation
    (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c))
    (heq : zeroReserve (X * Xᴴ) = zeroReserve (Y * Yᴴ))
    (hsat : coherentReserveMixed (X * Xᴴ) (Y * Yᴴ) + zeroReserve (X * Yᴴ) =
      -Real.sqrt (zeroReserve (X * Xᴴ) * zeroReserve (Y * Yᴴ)))
    (z : ℂ) (hz : Complex.normSq z = 1) :
    zeroReserve (coherentPositiveSource X Y z) = 0 :=
  coherentPositiveSource_reserve_zero_of_average X Y hn
    (coherentPositiveSource_average_zero_of_saturation X Y hn heq hsat) z hz

end ThreeCopyQutritWerner
