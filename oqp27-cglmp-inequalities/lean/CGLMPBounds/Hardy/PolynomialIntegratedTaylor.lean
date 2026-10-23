module

public import CGLMPBounds.Hardy.PolynomialAffineTrace

@[expose] public section


/-! A finite, explicit polynomial obtained by integrating the scalar Taylor
coefficients. Its evaluation and each coefficient are proved from finite
linearity of the Bochner integral, not from differentiation under an integral. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Polynomial MeasureTheory

def integratedAffinePolynomial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℂ[X]) (A B : Ω → ℂ) : ℂ[X] :=
  ∑ k ∈ Finset.range (f.natDegree + 1),
    C (∫ p, (Polynomial.hasseDeriv k f).eval (A p) * B p ^ k ∂μ) * X ^ k

lemma integratedAffinePolynomial_coeff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℂ[X]) (A B : Ω → ℂ) (k : ℕ) :
    (integratedAffinePolynomial μ f A B).coeff k =
      ∫ p, (Polynomial.hasseDeriv k f).eval (A p) * B p ^ k ∂μ := by
  classical
  by_cases hk : k < f.natDegree + 1
  · simp [integratedAffinePolynomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow, hk]
  · have hz := Polynomial.hasseDeriv_eq_zero_of_lt_natDegree f k (by omega)
    simp [integratedAffinePolynomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow, hk, hz]

lemma polynomial_eval_affine_eq_hasse_sum (f : ℂ[X]) (a b t : ℂ) :
    f.eval (a + t * b) =
      ∑ k ∈ Finset.range (f.natDegree + 1),
        ((Polynomial.hasseDeriv k f).eval a * b ^ k) * t ^ k := by
  rw [add_comm a, ← Polynomial.taylor_eval a f (t * b)]
  rw [(Polynomial.taylor a f).eval_eq_sum_range'
    (n := f.natDegree + 1) (by rw [Polynomial.natDegree_taylor]; omega) (t * b)]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.taylor_coeff, mul_pow]
  ring

theorem eval_integratedAffinePolynomial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℂ[X]) (A B : Ω → ℂ)
    (hI : ∀ k : ℕ, Integrable (fun p => (Polynomial.hasseDeriv k f).eval (A p) * B p ^ k) μ)
    (t : ℂ) :
    (integratedAffinePolynomial μ f A B).eval t = ∫ p, f.eval (A p + t * B p) ∂μ := by
  have hfun : (fun p => f.eval (A p + t * B p)) =
      (fun p => ∑ k ∈ Finset.range (f.natDegree + 1),
        ((Polynomial.hasseDeriv k f).eval (A p) * B p ^ k) * t ^ k) := by
    funext p
    exact polynomial_eval_affine_eq_hasse_sum f (A p) (B p) t
  rw [hfun, integral_finsetSum _ (fun k _ => (hI k).mul_const (t ^ k))]
  simp only [integratedAffinePolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    integral_mul_const]

lemma hasseDeriv_eval_eq_iterated_derivative_div (f : ℂ[X]) (k : ℕ) (z : ℂ) :
    (Polynomial.hasseDeriv k f).eval z =
      ((Polynomial.derivative^[k]) f).eval z / (k.factorial : ℂ) := by
  have he := congrArg (fun p : ℂ[X] => p.eval z)
    (congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) (k := k)) f)
  change (k.factorial • (Polynomial.hasseDeriv k f)).eval z =
    ((Polynomial.derivative^[k]) f).eval z at he
  rw [Polynomial.eval_smul] at he
  simp only [nsmul_eq_mul] at he
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply (eq_div_iff hk).mpr
  simpa only [mul_comm] using he

lemma iterate_derivative_second_derivative (f : ℂ[X]) (k : ℕ) :
    (Polynomial.derivative^[k]) f.derivative.derivative =
      (Polynomial.derivative^[k + 2]) f := by
  rw [show k + 2 = (k + 1) + 1 by omega, Function.iterate_succ_apply,
    Function.iterate_succ_apply]

lemma second_integratedAffinePolynomial_coeff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℂ[X]) (A B : Ω → ℂ) (k : ℕ) :
    (X ^ 2 * integratedAffinePolynomial μ f.derivative.derivative A B).coeff (k + 2) =
      (∫ p, ((Polynomial.derivative^[k + 2]) f).eval (A p) * B p ^ k ∂μ) /
        (k.factorial : ℂ) := by
  rw [Polynomial.coeff_X_pow_mul, integratedAffinePolynomial_coeff]
  simp_rw [hasseDeriv_eval_eq_iterated_derivative_div, iterate_derivative_second_derivative]
  have hfun : (fun p =>
      (((Polynomial.derivative^[k + 2]) f).eval (A p) / (k.factorial : ℂ)) * B p ^ k) =
      (fun p => (((Polynomial.derivative^[k + 2]) f).eval (A p) * B p ^ k) /
        (k.factorial : ℂ)) := by
    funext p
    ring
  rw [hfun, integral_div]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pinchingIntegralPolynomial (B Y : Matrix ι ι ℂ) (f : ℂ[X]) (s : ℂ) : ℂ[X] :=
  X ^ 2 * integratedAffinePolynomial (positivePinchingMeasure B Y)
    f.derivative.derivative (fun p : ℝ × ℝ => -s * p.1) (fun p => p.2)

lemma pinchingIntegralPolynomial_low_coefficients (B Y : Matrix ι ι ℂ) (f : ℂ[X]) (s : ℂ) :
    (pinchingIntegralPolynomial B Y f s).coeff 0 = 0 ∧
      (pinchingIntegralPolynomial B Y f s).coeff 1 = 0 := by
  simp only [pinchingIntegralPolynomial, Polynomial.coeff_X_pow_mul']
  norm_num

lemma pinchingIntegralPolynomial_coeff (B Y : Matrix ι ι ℂ) (f : ℂ[X]) (s : ℂ) (k : ℕ) :
    (pinchingIntegralPolynomial B Y f s).coeff (k + 2) =
      (∫ p : ℝ × ℝ, ((Polynomial.derivative^[k + 2]) f).eval (-s * p.1) *
        (p.2 : ℂ) ^ k ∂positivePinchingMeasure B Y) / (k.factorial : ℂ) :=
  second_integratedAffinePolynomial_coeff _ f _ _ k

lemma positivePinching_integratedAffine_integrable [Nonempty ι]
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) (f : ℂ[X]) {A D : (ℝ × ℝ) → ℂ}
    (hA : Continuous A) (hD : Continuous D) (k : ℕ) :
    Integrable (fun p => (Polynomial.hasseDeriv k f).eval (A p) * D p ^ k)
      (positivePinchingMeasure B Y) := by
  apply positivePinching_continuous_integrable hB hB2 hY
  exact ((Polynomial.hasseDeriv k f).continuous.comp hA).mul (hD.pow k)

theorem eval_pinchingIntegralPolynomial [Nonempty ι]
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) (f : ℂ[X]) (s t : ℂ) :
    (pinchingIntegralPolynomial B Y f s).eval t =
      t ^ 2 * ∫ p : ℝ × ℝ, f.derivative.derivative.eval (-s * p.1 + t * p.2)
        ∂positivePinchingMeasure B Y := by
  rw [pinchingIntegralPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [eval_integratedAffinePolynomial _ _ _ _
    (positivePinching_integratedAffine_integrable hB hB2 hY f.derivative.derivative
      (by fun_prop) (by fun_prop))]

end
end CGLMPBounds.Hardy
