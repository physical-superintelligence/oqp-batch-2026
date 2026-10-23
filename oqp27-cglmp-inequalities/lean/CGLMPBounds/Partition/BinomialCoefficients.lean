module

public import CGLMPBounds.Partition.BinomialDerivatives

@[expose] public section


/-! Identification of the source polynomial coefficients with the literal
binomial weight and its actual second derivative. No atom law is assumed. -/

namespace CGLMPBounds.Partition
open Polynomial
noncomputable section

theorem boundaryBinomialPolynomial_coeff (d h : ℕ) (x : ℝ) :
    (boundaryBinomialPolynomial d x).coeff h = (scalarBinomialWeight d h x : ℂ) := by
  have hp : boundaryBinomialPolynomial d x =
      ((Polynomial.X + Polynomial.C ((1 - x : ℝ) : ℂ)) ^ d).comp
        (Polynomial.C (x : ℂ) * Polynomial.X) := by
    simp [boundaryBinomialPolynomial, Polynomial.pow_comp, add_comm]
  rw [hp, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_X_add_C_pow]
  simp only [scalarBinomialWeight, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  ring

lemma coeff_X_sub_one_sq_mul (p : Polynomial ℂ) (h : ℕ) :
    (((Polynomial.X - 1) ^ 2) * p).coeff h =
      p.coeff h - 2 * (if 1 ≤ h then p.coeff (h - 1) else 0) +
        (if 2 ≤ h then p.coeff (h - 2) else 0) := by
  have hp : (Polynomial.X - 1) ^ 2 * p =
      Polynomial.X ^ 2 * p - Polynomial.C (2 : ℂ) * (Polynomial.X ^ 1 * p) + p := by
    rw [Polynomial.C_ofNat]
    ring
  rw [hp]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  ring

theorem fourierCountPolynomial_coeff (d n h : ℕ) (hd : 2 ≤ d) (x : ℝ) :
    (fourierCountPolynomial d n x).coeff h =
      ((scalarBinomialWeight d h x + fourierTiltShape n x / d *
        iteratedDeriv 2 (scalarBinomialWeight d h) x : ℝ) : ℂ) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [fourierCountPolynomial, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    coeff_X_sub_one_sq_mul]
  simp_rw [boundaryBinomialPolynomial_coeff]
  rcases h with _ | h
  · rw [iteratedDeriv_two_scalarBinomialWeight_zero d hd x]
    norm_num
    push_cast
    field_simp [hdC]
  · rcases h with _ | h
    · rw [iteratedDeriv_two_scalarBinomialWeight_one d hd x]
      norm_num
      push_cast
      field_simp [hdC]
    · change _ = ((scalarBinomialWeight d (h + 2) x + fourierTiltShape n x / d *
        iteratedDeriv 2 (scalarBinomialWeight d (h + 2)) x : ℝ) : ℂ)
      rw [iteratedDeriv_two_scalarBinomialWeight_add_two d h hd x]
      have hh1 : 1 ≤ h + 2 := by omega
      have hh2 : 2 ≤ h + 2 := by omega
      simp only [show h.succ.succ = h + 2 by omega, if_pos hh1, if_pos hh2,
        show h + 2 - 1 = h + 1 by omega, Nat.add_sub_cancel]
      push_cast
      field_simp [hdC]

end
end CGLMPBounds.Partition
