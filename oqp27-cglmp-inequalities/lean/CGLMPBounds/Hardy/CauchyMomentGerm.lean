module

public import CGLMPBounds.Hardy.CompactParametricIntegral
public import CGLMPBounds.Hardy.SpectralTracePolynomial

@[expose] public section


/-! The genuine resolvent germ obtained from polynomial moments in C.5.
The second-derivative kernel is summed by the convergent binomial series.
The finite measure integral is differentiated using compactness, rather than
assuming a resolvent identity or an interchange of infinite sums. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Polynomial Filter Set MeasureTheory
open scoped Topology

lemma second_monomial_eval (n : ℕ) (a : ℂ) :
    (X ^ n : ℂ[X]).derivative.derivative.eval a =
      (n.descFactorial 2 : ℂ) * a ^ (n - 2) := by
  change ((Polynomial.derivative^[2]) (X ^ n : ℂ[X])).eval a = _
  rw [Polynomial.iterate_derivative_X_pow_eq_C_mul]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

lemma hasSum_second_derivative_geometric {w a : ℂ} (h : ‖w * a‖ < 1) :
    HasSum (fun n : ℕ => (X ^ n : ℂ[X]).derivative.derivative.eval a * w ^ n)
      (2 * w ^ 2 / (1 - w * a) ^ 3) := by
  rw [← hasSum_nat_add_iff' 2]
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one 2 h).mul_left (2 * w ^ 2)
  convert hs using 1
  · funext n
    rw [second_monomial_eval]
    have hn : ((n + 2).descFactorial 2 : ℂ) =
        2 * (((n + 2).choose 2 : ℕ) : ℂ) := by
      simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      norm_num
    rw [hn, Nat.add_sub_cancel, pow_add, mul_pow]
    ring
  · norm_num [Finset.sum_range_succ, Polynomial.derivative_X_pow]
    ring

lemma hasFPowerSeriesAt_second_derivative_geometric (a : ℂ) :
    HasFPowerSeriesAt (fun w : ℂ => 2 * w ^ 2 / (1 - w * a) ^ 3)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => (X ^ n : ℂ[X]).derivative.derivative.eval a)) 0 := by
  have hc : ContinuousAt (fun w : ℂ => ‖w * a‖) 0 := by fun_prop
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [hc.eventually_lt continuousAt_const (show ‖(0 : ℂ) * a‖ < 1 by simp)]
    with w hw
  simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, mul_comm]
    using hasSum_second_derivative_geometric hw

lemma second_derivative_geometric_taylor_coefficient (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun w : ℂ => 2 * w ^ 2 / (1 - w * a) ^ 3) 0 /
      (n.factorial : ℂ) = (X ^ n : ℂ[X]).derivative.derivative.eval a := by
  have hp := hasFPowerSeriesAt_second_derivative_geometric a
  have he := hp.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hp
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he

lemma multiset_geometric_taylor_coefficient (s : Multiset ℂ) (n : ℕ) :
    iteratedDeriv n (fun w : ℂ => (s.map (fun a => 1 / (1 - w * a))).sum) 0 /
      (n.factorial : ℂ) = (s.map (fun a => a ^ n)).sum := by
  have hp := hasFPowerSeriesAt_multiset_geometric s
  have he := hp.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hp
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he

lemma analytic_eventually_zero_of_taylor_coefficients {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z)
    (hc : ∀ n : ℕ, iteratedDeriv n f z / (n.factorial : ℂ) = 0) :
    ∀ᶠ w in 𝓝 z, f w = 0 := by
  have hp := hf.hasFPowerSeriesAt
  have he : (fun n : ℕ => iteratedDeriv n f z / (n.factorial : ℂ)) = 0 := funext hc
  rw [he, FormalMultilinearSeries.ofScalars_series_eq_zero_of_scalar_zero] at hp
  exact hp.eventually_eq_zero

theorem cauchy_moment_resolvent_germ
    (P Q : Multiset ℂ) (r : ℂ) {K : Set ℂ} (hK : IsCompact K)
    (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hmoment : ∀ n : ℕ,
      (P.map (fun a => a ^ n)).sum / r - (Q.map (fun a => a ^ n)).sum / r =
        -(∫ ζ in K, (X ^ n : ℂ[X]).derivative.derivative.eval ζ ∂μ)) :
    ∀ᶠ w : ℂ in 𝓝 0,
      (P.map (fun a => 1 / (1 - w * a))).sum / r -
        (Q.map (fun a => 1 / (1 - w * a))).sum / r =
          -(∫ ζ in K, 2 * w ^ 2 / (1 - w * ζ) ^ 3 ∂μ) := by
  let G : ℂ → ℂ := fun w =>
    (P.map (fun a => 1 / (1 - w * a))).sum / r -
      (Q.map (fun a => 1 / (1 - w * a))).sum / r
  let H : ℂ → ℂ := fun w => ∫ ζ in K, 2 * w ^ 2 / (1 - w * ζ) ^ 3 ∂μ
  have hP := (hasFPowerSeriesAt_multiset_geometric P).analyticAt
  have hQ := (hasFPowerSeriesAt_multiset_geometric Q).analyticAt
  have hG : AnalyticAt ℂ G 0 := (hP.div_const (c := r)).sub (hQ.div_const (c := r))
  have hkernel : ∀ ζ ∈ K, AnalyticAt ℂ
      (fun p : ℂ × ℂ => 2 * p.1 ^ 2 / (1 - p.1 * p.2) ^ 3) (0, ζ) := by
    intro ζ _
    apply (analyticAt_const.mul (analyticAt_fst.pow 2)).div
      ((analyticAt_const.sub (analyticAt_fst.mul analyticAt_snd)).pow 3)
    simp
  have hH : AnalyticAt ℂ H 0 := analyticAt_integral_compact_joint hK μ hkernel
  have hz : ∀ᶠ w in 𝓝 (0 : ℂ), G w + H w = 0 := by
    apply analytic_eventually_zero_of_taylor_coefficients (hG.add hH)
    intro n
    have hGcoeff : iteratedDeriv n G 0 / (n.factorial : ℂ) =
        (P.map (fun a => a ^ n)).sum / r - (Q.map (fun a => a ^ n)).sum / r := by
      rw [show G = (fun w : ℂ =>
        (P.map (fun a => 1 / (1 - w * a))).sum / r -
          (Q.map (fun a => 1 / (1 - w * a))).sum / r) from rfl,
        iteratedDeriv_fun_sub (hP.div_const (c := r)).contDiffAt (hQ.div_const (c := r)).contDiffAt,
        iteratedDeriv_div_const, iteratedDeriv_div_const, sub_div]
      have hdiv (a : ℂ) : a / r / (n.factorial : ℂ) = a / (n.factorial : ℂ) / r := by ring
      rw [hdiv, hdiv, multiset_geometric_taylor_coefficient, multiset_geometric_taylor_coefficient]
    have hHcoeff : iteratedDeriv n H 0 / (n.factorial : ℂ) =
        ∫ ζ in K, (X ^ n : ℂ[X]).derivative.derivative.eval ζ ∂μ := by
      rw [show H = (fun w : ℂ => ∫ ζ in K, 2 * w ^ 2 / (1 - w * ζ) ^ 3 ∂μ) from rfl,
        iteratedDeriv_integral_compact_joint n hK μ hkernel, ← integral_div]
      apply setIntegral_congr_fun hK.measurableSet
      intro ζ _
      exact second_derivative_geometric_taylor_coefficient ζ n
    rw [iteratedDeriv_add hG.contDiffAt hH.contDiffAt, add_div, hGcoeff, hHcoeff,
      hmoment n, neg_add_cancel]
  filter_upwards [hz] with w hw
  exact eq_neg_of_add_eq_zero_left hw

end
end CGLMPBounds.Hardy
