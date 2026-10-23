module

public import CGLMPBounds.Hardy.PolynomialMixedTaylor
public import CGLMPBounds.Hardy.PositivePinchingBetaMoments

@[expose] public section


/-! Matching the actual t^(m+2) coefficient to the actual C.11 measure.
The argument uses genuine contours for nonzero real s. Extension to s=0,
polynomial reconstruction in t, and general-basis transport remain separate. -/

open scoped Polynomial

namespace CGLMPBounds.Hardy
noncomputable section
open Complex Matrix Metric Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma monomial_iterated_derivative_degree_factor (N k : ℕ) (z : ℂ) :
    ((Polynomial.derivative^[k + 1]) (Polynomial.X ^ N : ℂ[X])).eval z =
      (N : ℂ) * ((Polynomial.derivative^[k]) (Polynomial.X ^ (N - 1) : ℂ[X])).eval z := by
  rw [Function.iterate_succ_apply, Polynomial.derivative_X_pow,
    Polynomial.iterate_derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]

lemma polynomialBetaDividedDifference_degree_factor (N p q : ℕ) (s : ℂ) :
    (N : ℂ) * polynomialBetaDividedDifference (Polynomial.X ^ (N - 1)) s (-s) p q =
      (1 / ((p.factorial : ℂ) * (q.factorial : ℂ))) *
        ∫ u in (0 : ℝ)..1, (u : ℂ) ^ p * (1 - (u : ℂ)) ^ q *
          ((Polynomial.derivative^[p + q + 2]) (Polynomial.X ^ N : ℂ[X])).eval
            (-s * (1 - 2 * (u : ℂ))) := by
  have hfun : (fun u : ℝ => (u : ℂ) ^ p * (1 - (u : ℂ)) ^ q *
      ((Polynomial.derivative^[p + q + 2]) (Polynomial.X ^ N : ℂ[X])).eval
        (-s * (1 - 2 * (u : ℂ)))) =
      (fun u : ℝ => (N : ℂ) * ((u : ℂ) ^ p * (1 - (u : ℂ)) ^ q *
        ((Polynomial.derivative^[p + q + 1]) (Polynomial.X ^ (N - 1) : ℂ[X])).eval
          ((u : ℂ) * s + (1 - (u : ℂ)) * (-s)))) := by
    funext u
    rw [show p + q + 2 = (p + q + 1) + 1 by omega,
      monomial_iterated_derivative_degree_factor]
    rw [show -s * (1 - 2 * (u : ℂ)) = (u : ℂ) * s + (1 - (u : ℂ)) * (-s) by ring]
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  unfold polynomialBetaDividedDifference
  ring

theorem positivePinching_diagonal_monomial_coefficient [Nonempty ι]
    (σ : ι → Bool) {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (m : ℕ) {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : s ≠ 0) :
    let B := involutionFromSigns σ
    let C := positivePinchingPart B Y
    iteratedDeriv (m + 2) (fun t : ℂ => Matrix.trace (((s : ℂ) • B + t • Y) ^ N)) 0 /
        (((m + 2).factorial : ℂ) * (Fintype.card ι : ℂ)) -
      iteratedDeriv (m + 2) (fun t : ℂ => Matrix.trace (((s : ℂ) • B + t • C) ^ N)) 0 /
        (((m + 2).factorial : ℂ) * (Fintype.card ι : ℂ)) =
      (∫ p : ℝ × ℝ,
        ((Polynomial.derivative^[m + 2]) (Polynomial.X ^ N : ℂ[X])).eval
          (-(s : ℂ) * p.1) * (p.2 : ℂ) ^ m ∂positivePinchingMeasure B Y) /
            (m.factorial : ℂ) := by
  classical
  let R : ℝ := |s| + 1
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have ha : (s : ℂ) ∈ ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    dsimp only [R]
    linarith
  have hb : ((-s : ℝ) : ℂ) ∈ ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    dsimp only [R]
    linarith
  have hab : s ≠ -s := by intro h; apply hs; linarith
  have hdiag : Matrix.diagonal (fun i => if σ i then (s : ℂ) else ((-s : ℝ) : ℂ)) =
      (s : ℂ) • involutionFromSigns σ := by
    ext i j
    by_cases hij : i = j
    · subst j
      cases hi : σ i <;> simp [involutionFromSigns, hi, Matrix.diagonal_apply, Matrix.smul_apply]
    · simp [involutionFromSigns, Matrix.diagonal_apply, Matrix.smul_apply, hij]
  have ht := diagonal_two_node_mixed_trace_taylor_coefficient σ hY m hN hab hR ha hb
  dsimp only at ht
  rw [hdiag] at ht
  let g : ℝ → ℂ := fun x =>
    ((Polynomial.derivative^[m + 2]) (Polynomial.X ^ N : ℂ[X])).eval (-(s : ℂ) * x)
  have hg : Continuous g := by dsimp only [g]; fun_prop
  have hν := positivePinching_diagonal_weighted_moment_eq_beta σ hY m hg
  dsimp only
  rw [ht, hν]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  let p := cyclePositiveCount σ v
  let q := m + 2 - p
  by_cases hp : 1 ≤ p ∧ p < m + 2
  · change _ * (if 1 ≤ p ∧ p < m + 2 then _ else _) =
      _ * (if 1 ≤ p ∧ p < m + 2 then _ else _)
    rw [if_pos hp, if_pos hp]
    have horder : p - 1 + (q - 1) + 2 = m + 2 := by dsimp only [q]; omega
    have hf := polynomialBetaDividedDifference_degree_factor N (p - 1) (q - 1) (s : ℂ)
    rw [horder] at hf
    have harg : (fun u : ℝ => (u : ℂ) ^ (p - 1) * (1 - (u : ℂ)) ^ (q - 1) *
        ((Polynomial.derivative^[m + 2]) (Polynomial.X ^ N : ℂ[X])).eval
          (-(s : ℂ) * (1 - 2 * (u : ℂ)))) =
        (fun u : ℝ => (u : ℂ) ^ (p - 1) * (1 - (u : ℂ)) ^ (q - 1) * g (1 - 2 * u)) := by
      funext u
      simp only [g, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
        Complex.ofReal_ofNat]
    rw [harg] at hf
    rw [← hf]
    simp only [p, q, Complex.ofReal_neg, div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  · change _ * (if 1 ≤ p ∧ p < m + 2 then _ else _) =
      _ * (if 1 ≤ p ∧ p < m + 2 then _ else _)
    simp only [if_neg hp, mul_zero]

end
end CGLMPBounds.Hardy
