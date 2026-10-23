module

public import CGLMPBounds.Hardy.PolynomialTwoCircleIntegral

@[expose] public section


/-! Polynomial two-node Hermite–Genocchi identity. Both sides are literal
integrals. Their recurrences are proved separately, with Cauchy and the
fundamental theorem supplying the boundary cases; no divided-difference
identity is assumed. -/

open scoped Polynomial

namespace CGLMPBounds.Hardy
noncomputable section
open Complex

def polynomialBetaDividedDifference (f : ℂ[X]) (a b : ℂ) (p q : ℕ) : ℂ :=
  (1 / ((p.factorial : ℂ) * q.factorial)) *
    ∫ u in (0 : ℝ)..1, (u : ℂ) ^ p * (1 - (u : ℂ)) ^ q *
      ((Polynomial.derivative^[p + q + 1]) f).eval ((u : ℂ) * a + (1 - (u : ℂ)) * b)

lemma polynomialBetaDividedDifference_zero_zero (f : ℂ[X]) (a b : ℂ) :
    (a - b) * polynomialBetaDividedDifference f a b 0 0 = f.eval a - f.eval b := by
  simpa [polynomialBetaDividedDifference] using polynomial_segment_fundamental f a b

lemma polynomialBetaDividedDifference_zero_succ (f : ℂ[X]) (a b : ℂ) (q : ℕ) :
    (a - b) * polynomialBetaDividedDifference f a b 0 (q + 1) =
      polynomialBetaDividedDifference f a b 0 q -
        ((Polynomial.derivative^[q + 1]) f).eval b / ((q + 1).factorial : ℂ) := by
  have h := polynomial_segment_beta_integrationByParts
    ((Polynomial.derivative^[q + 1]) f) a b 0 (q + 1)
  have hd : (((Polynomial.derivative^[q + 1]) f).derivative) =
      (Polynomial.derivative^[q + 1 + 1]) f := by
    exact (Function.iterate_succ_apply' Polynomial.derivative (q + 1) f).symm
  rw [hd] at h
  simp only [zero_pow (Nat.add_one_ne_zero q), pow_zero, Nat.cast_zero,
    zero_mul, one_mul, Nat.add_sub_cancel, sub_zero] at h
  unfold polynomialBetaDividedDifference
  simp only [Nat.zero_add, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero]
  rw [Nat.factorial_succ]
  push_cast
  have hfac : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have hq : (q : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  field_simp [hfac, hq]
  push_cast at h
  simp only [mul_comm a, mul_comm b] at h ⊢
  linear_combination h

lemma polynomialBetaDividedDifference_succ_zero (f : ℂ[X]) (a b : ℂ) (p : ℕ) :
    (a - b) * polynomialBetaDividedDifference f a b (p + 1) 0 =
      ((Polynomial.derivative^[p + 1]) f).eval a / ((p + 1).factorial : ℂ) -
        polynomialBetaDividedDifference f a b p 0 := by
  have h := polynomial_segment_beta_integrationByParts
    ((Polynomial.derivative^[p + 1]) f) a b (p + 1) 0
  have hd : (((Polynomial.derivative^[p + 1]) f).derivative) =
      (Polynomial.derivative^[p + 1 + 1]) f := by
    exact (Function.iterate_succ_apply' Polynomial.derivative (p + 1) f).symm
  rw [hd] at h
  simp only [zero_pow (Nat.add_one_ne_zero p), pow_zero, Nat.cast_zero,
    zero_mul, one_mul, Nat.add_sub_cancel, sub_zero, add_zero] at h
  unfold polynomialBetaDividedDifference
  simp only [Nat.add_zero, Nat.factorial_zero, Nat.cast_one, mul_one, pow_zero]
  rw [Nat.factorial_succ]
  push_cast
  have hfac : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hp : (p : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  field_simp [hfac, hp]
  push_cast at h
  simp only [mul_one, mul_comm a, mul_comm b] at h ⊢
  linear_combination h

lemma polynomialBetaDividedDifference_succ_succ (f : ℂ[X]) (a b : ℂ) (p q : ℕ) :
    (a - b) * polynomialBetaDividedDifference f a b (p + 1) (q + 1) =
      polynomialBetaDividedDifference f a b (p + 1) q -
        polynomialBetaDividedDifference f a b p (q + 1) := by
  have h := polynomial_segment_beta_integrationByParts
    ((Polynomial.derivative^[p + q + 2]) f) a b (p + 1) (q + 1)
  have hd : (((Polynomial.derivative^[p + q + 2]) f).derivative) =
      (Polynomial.derivative^[p + q + 3]) f := by
    simpa only [show p + q + 3 = (p + q + 2) + 1 by omega] using
      (Function.iterate_succ_apply' Polynomial.derivative (p + q + 2) f).symm
  rw [hd] at h
  simp only [zero_pow (Nat.add_one_ne_zero p), zero_pow (Nat.add_one_ne_zero q),
    zero_mul, sub_zero, Nat.add_sub_cancel] at h
  unfold polynomialBetaDividedDifference
  rw [show p + 1 + (q + 1) + 1 = p + q + 3 by omega,
    show p + 1 + q + 1 = p + q + 2 by omega,
    show p + (q + 1) + 1 = p + q + 2 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hfacp : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hfacq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have hp : (p : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  have hq : (q : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  field_simp [hfacp, hfacq, hp, hq]
  push_cast at h
  simp only [mul_comm a, mul_comm b] at h ⊢
  linear_combination h

theorem polynomialTwoCircleIntegral_eq_beta (f : ℂ[X]) {a b : ℂ}
    (hab : a ≠ b) (p q : ℕ) :
    polynomialTwoCircleIntegral f a b (p + 1) (q + 1) =
      polynomialBetaDividedDifference f a b p q := by
  have hab0 : a - b ≠ 0 := sub_ne_zero.mpr hab
  induction p generalizing q with
  | zero =>
    induction q with
    | zero =>
      apply mul_left_cancel₀ hab0
      rw [polynomialTwoCircleIntegral_recurrence f hab 0 0,
        polynomialTwoCircleIntegral_left_axis f hab 0,
        polynomialTwoCircleIntegral_right_axis f hab 0,
        polynomialBetaDividedDifference_zero_zero]
      simp
    | succ q ih =>
      apply mul_left_cancel₀ hab0
      rw [polynomialTwoCircleIntegral_recurrence f hab 0 (q + 1),
        polynomialTwoCircleIntegral_right_axis f hab (q + 1),
        polynomialBetaDividedDifference_zero_succ, ih]
  | succ p ihp =>
    induction q with
    | zero =>
      apply mul_left_cancel₀ hab0
      rw [polynomialTwoCircleIntegral_recurrence f hab (p + 1) 0,
        polynomialTwoCircleIntegral_left_axis f hab (p + 1),
        polynomialBetaDividedDifference_succ_zero, ihp 0]
    | succ q ihq =>
      apply mul_left_cancel₀ hab0
      rw [polynomialTwoCircleIntegral_recurrence f hab (p + 1) (q + 1),
        polynomialBetaDividedDifference_succ_succ, ihq, ihp (q + 1)]

end
end CGLMPBounds.Hardy
