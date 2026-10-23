module

public import CGLMPBounds.Defs.PartitionCount

@[expose] public section


/-! Exact second derivatives of the literal scalar binomial weights, with
the h=0 and h=1 boundary cases retained. The proof uses Mathlib's actual
Bernstein polynomials, not a supplied derivative identity. -/

namespace CGLMPBounds.Partition
open Polynomial
noncomputable section

lemma bernsteinPolynomial_eval_scalar (d h : ℕ) (x : ℝ) :
    (bernsteinPolynomial ℝ d h).eval x = scalarBinomialWeight d h x := by
  simp [bernsteinPolynomial, scalarBinomialWeight]

lemma iteratedDeriv_scalarBinomialWeight_eq (d h : ℕ) (x : ℝ) :
    iteratedDeriv 2 (scalarBinomialWeight d h) x =
      (bernsteinPolynomial ℝ d h).derivative.derivative.eval x := by
  have hfun : scalarBinomialWeight d h = fun t => (bernsteinPolynomial ℝ d h).eval t := by
    funext t
    exact (bernsteinPolynomial_eval_scalar d h t).symm
  rw [hfun]
  rw [iteratedDeriv_eq_iterate]
  change deriv (fun t : ℝ => deriv (fun u : ℝ => (bernsteinPolynomial ℝ d h).eval u) t) x = _
  simp only [Polynomial.deriv]

theorem iteratedDeriv_two_scalarBinomialWeight_zero (d : ℕ) (hd : 2 ≤ d) (x : ℝ) :
    iteratedDeriv 2 (scalarBinomialWeight d 0) x =
      (d : ℝ) * ((d : ℝ) - 1) * scalarBinomialWeight (d - 2) 0 x := by
  have hcast : ((d - 1 : ℕ) : Polynomial ℝ) = (d : Polynomial ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one]
  have hp : (bernsteinPolynomial ℝ d 0).derivative.derivative =
      (d : Polynomial ℝ) * ((d : Polynomial ℝ) - 1) *
        bernsteinPolynomial ℝ (d - 2) 0 := by
    simp only [bernsteinPolynomial.derivative_zero, Polynomial.derivative_mul,
      Polynomial.derivative_neg, Polynomial.derivative_natCast,
      neg_zero, zero_mul, zero_add, Nat.sub_sub]
    rw [hcast]
    ring
  rw [iteratedDeriv_scalarBinomialWeight_eq, hp]
  simp [bernsteinPolynomial_eval_scalar]

theorem iteratedDeriv_two_scalarBinomialWeight_one (d : ℕ) (hd : 2 ≤ d) (x : ℝ) :
    iteratedDeriv 2 (scalarBinomialWeight d 1) x =
      (d : ℝ) * ((d : ℝ) - 1) *
        (scalarBinomialWeight (d - 2) 1 x - 2 * scalarBinomialWeight (d - 2) 0 x) := by
  have hcast : ((d - 1 : ℕ) : Polynomial ℝ) = (d : Polynomial ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one]
  have hp : (bernsteinPolynomial ℝ d 1).derivative.derivative =
      (d : Polynomial ℝ) * ((d : Polynomial ℝ) - 1) *
        (bernsteinPolynomial ℝ (d - 2) 1 - 2 * bernsteinPolynomial ℝ (d - 2) 0) := by
    simp only [bernsteinPolynomial.derivative_succ, bernsteinPolynomial.derivative_zero,
      Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_neg,
      Polynomial.derivative_natCast, neg_zero, zero_mul, zero_add, Nat.sub_sub]
    rw [hcast]
    ring
  rw [iteratedDeriv_scalarBinomialWeight_eq, hp]
  simp [bernsteinPolynomial_eval_scalar]

theorem iteratedDeriv_two_scalarBinomialWeight_add_two
    (d h : ℕ) (hd : 2 ≤ d) (x : ℝ) :
    iteratedDeriv 2 (scalarBinomialWeight d (h + 2)) x =
      (d : ℝ) * ((d : ℝ) - 1) *
        (scalarBinomialWeight (d - 2) (h + 2) x -
          2 * scalarBinomialWeight (d - 2) (h + 1) x + scalarBinomialWeight (d - 2) h x) := by
  have hcast : ((d - 1 : ℕ) : Polynomial ℝ) = (d : Polynomial ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one]
  have hp : (bernsteinPolynomial ℝ d (h + 2)).derivative.derivative =
      (d : Polynomial ℝ) * ((d : Polynomial ℝ) - 1) *
        (bernsteinPolynomial ℝ (d - 2) (h + 2) -
          2 * bernsteinPolynomial ℝ (d - 2) (h + 1) + bernsteinPolynomial ℝ (d - 2) h) := by
    simp only [bernsteinPolynomial.derivative_succ, Polynomial.derivative_mul,
      Polynomial.derivative_sub, Polynomial.derivative_natCast,
      zero_mul, zero_add, Nat.sub_sub]
    rw [hcast]
    ring
  rw [iteratedDeriv_scalarBinomialWeight_eq, hp]
  simp [bernsteinPolynomial_eval_scalar]

end
end CGLMPBounds.Partition
