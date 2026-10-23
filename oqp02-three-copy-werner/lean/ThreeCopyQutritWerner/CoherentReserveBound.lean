module

public import ThreeCopyQutritWerner.CoherentReservePencil
public import Mathlib.Algebra.QuadraticDiscriminant

@[expose] public section


/-!
# Radial minimization of the actual coherent reserve

Four-phase positivity holds after every real rescaling of the second factor.
Its quartic polynomial gives the geometric-mean bound, including zero-reserve
end cases. This supplies the coherent bound B_P, not the separate shadow bound.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

/-- A nonnegative even quartic has middle coefficient at least minus the
geometric mean of its nonnegative constant and leading coefficients. -/
theorem coherent_quartic_middle_bound (a b c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ a + 2 * t ^ 2 * b + t ^ 4 * c) :
    -Real.sqrt (a * c) ≤ b := by
  by_cases hb : 0 ≤ b
  · exact (neg_nonpos.mpr (Real.sqrt_nonneg _)).trans hb
  have hquad : ∀ x : ℝ, 0 ≤ c * (x * x) + (2 * b) * x + a := by
    intro x
    by_cases hx : 0 ≤ x
    · have hh := h (Real.sqrt x)
      have hs := Real.sq_sqrt hx
      have hs4 : (Real.sqrt x) ^ 4 = x ^ 2 := by
        calc
          _ = ((Real.sqrt x) ^ 2) ^ 2 := by ring
          _ = x ^ 2 := by rw [hs]
      rw [hs4, hs] at hh
      nlinarith
    · have hm : 0 ≤ (2 * b) * x := mul_nonneg_of_nonpos_of_nonpos
        (by linarith) (le_of_not_ge hx)
      have hs := mul_nonneg hc (mul_self_nonneg x)
      linarith
  have hd := discrim_le_zero hquad
  dsimp [discrim] at hd
  have hs := Real.sq_sqrt (mul_nonneg ha hc)
  have hn := Real.sqrt_nonneg (a * c)
  nlinarith

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- Every real radial rescaling obeys the exact reserve quartic. -/
theorem coherentReserve_radial_nonneg (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) (t : ℝ) :
    0 ≤ zeroReserve (X * Xᴴ) +
      2 * t ^ 2 * (coherentReserveMixed (X * Xᴴ) (Y * Yᴴ) + zeroReserve (X * Yᴴ)) +
      t ^ 4 * zeroReserve (Y * Yᴴ) := by
  have he : ((t : ℂ) • Y) * ((t : ℂ) • Y)ᴴ =
      ((t ^ 2 : ℝ) : ℂ) • (Y * Yᴴ) := by
    simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.ofReal_pow, pow_two, Complex.ofReal_mul]
  have hcross : X * ((t : ℂ) • Y)ᴴ = (t : ℂ) • (X * Yᴴ) := by
    simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.mul_smul]
  have h := coherentPositiveSource_reserve_pair_bound X ((t : ℂ) • Y) hn
  rw [he, hcross, zeroReserve_smul, Complex.normSq_ofReal] at h
  have hm := zeroReserve_real_mix (X * Xᴴ) (Y * Yᴴ) 1 (t ^ 2)
  simp only [Complex.ofReal_one, one_smul, one_pow, one_mul] at hm
  rw [hm] at h
  nlinarith

/-- The full geometric-mean coherent bound, with no balanced-factor or
normality assumption and with zero-reserve cases included. -/
theorem coherentReserve_ge_neg_mixed_sqrt (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) :
    -coherentReserveMixed (X * Xᴴ) (Y * Yᴴ) -
      Real.sqrt (zeroReserve (X * Xᴴ) * zeroReserve (Y * Yᴴ)) ≤ zeroReserve (X * Yᴴ) := by
  have hx : 0 ≤ zeroReserve (X * Xᴴ) := by
    simpa [coherentPositiveSource] using coherentPositiveSource_reserve_nonneg X 0 0 hn
  have hy : 0 ≤ zeroReserve (Y * Yᴴ) := by
    simpa [coherentPositiveSource] using coherentPositiveSource_reserve_nonneg Y 0 0 hn
  have h := coherent_quartic_middle_bound (zeroReserve (X * Xᴴ))
    (coherentReserveMixed (X * Xᴴ) (Y * Yᴴ) + zeroReserve (X * Yᴴ))
    (zeroReserve (Y * Yᴴ)) hx hy (coherentReserve_radial_nonneg X Y hn)
  linarith

/-- The actual manuscript-normalized coherent endpoint lower bound B_P.
The additional shadow inequality and its equality analysis remain separate. -/
theorem coherentEndpoint_lower_bound (X Y : Matrix (a × b × c) (Fin 2) ℂ)
    (hn : 2 ≤ Fintype.card (a × b × c)) :
    (2 * invN (X * Yᴴ) - invT (X * Yᴴ)) / 8 -
      coherentReserveMixed (X * Xᴴ) (Y * Yᴴ) -
      Real.sqrt (zeroReserve (X * Xᴴ) * zeroReserve (Y * Yᴴ)) ≤ endpointEnergy (X * Yᴴ) := by
  have h := coherentReserve_ge_neg_mixed_sqrt X Y hn
  rw [zeroReserve_eq_endpoint (X * Yᴴ)] at h
  linarith

end ThreeCopyQutritWerner
