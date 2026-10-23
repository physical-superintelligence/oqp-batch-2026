module

public import CGLMPBounds.Hardy.CauchyMomentGerm

@[expose] public section


/-! Polynomial moments determine the actual Cauchy transform on a disk
in the inverse coordinate. The finite root sums retain multiplicity.
The scalar factor is explicit; this supports general complex t in C.10. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Polynomial Filter Set MeasureTheory Metric
open scoped Topology

theorem weighted_cauchy_moment_resolvent_germ
    (P Q : Multiset ℂ) (r σ : ℂ) {K : Set ℂ} (hK : IsCompact K)
    (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hmoment : ∀ n : ℕ,
      (P.map (fun a => a ^ n)).sum / r - (Q.map (fun a => a ^ n)).sum / r =
        σ * (∫ ζ in K, (X ^ n : ℂ[X]).derivative.derivative.eval ζ ∂μ)) :
    ∀ᶠ w : ℂ in 𝓝 0,
      (P.map (fun a => 1 / (1 - w * a))).sum / r -
        (Q.map (fun a => 1 / (1 - w * a))).sum / r =
          σ * (∫ ζ in K, 2 * w ^ 2 / (1 - w * ζ) ^ 3 ∂μ) := by
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
  have hz : ∀ᶠ w in 𝓝 (0 : ℂ), G w - σ * H w = 0 := by
    apply analytic_eventually_zero_of_taylor_coefficients (hG.fun_sub ((analyticAt_const (v := σ)).fun_mul hH))
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
    rw [iteratedDeriv_fun_sub hG.contDiffAt ((analyticAt_const (v := σ)).fun_mul hH).contDiffAt,
      iteratedDeriv_const_mul_field, sub_div, mul_div_assoc, hGcoeff, hHcoeff,
      hmoment n, sub_self]
  filter_upwards [hz] with w hw
  exact sub_eq_zero.mp hw


lemma one_sub_mul_ne_zero_of_norm_bound {w a : ℂ} {M : ℝ}
    (hM : 0 < M) (hw : ‖w‖ < 1 / M) (ha : ‖a‖ ≤ M) :
    1 - w * a ≠ 0 := by
  have hm : ‖w * a‖ < 1 := by
    rw [norm_mul]
    calc
      ‖w‖ * ‖a‖ ≤ ‖w‖ * M := mul_le_mul_of_nonneg_left ha (norm_nonneg _)
      _ < (1 / M) * M := mul_lt_mul_of_pos_right hw hM
      _ = 1 := by field_simp
  intro hz
  have he : w * a = 1 := (sub_eq_zero.mp hz).symm
  simpa only [he, norm_one, lt_self_iff_false] using hm

lemma analyticAt_multiset_geometric_away (s : Multiset ℂ) {w : ℂ}
    (h : ∀ a ∈ s, 1 - w * a ≠ 0) :
    AnalyticAt ℂ (fun z => (s.map (fun a => 1 / (1 - z * a))).sum) w := by
  revert h
  induction s using Multiset.induction_on with
  | empty => intro _; simpa using (analyticAt_const (v := (0 : ℂ)))
  | @cons a s ih =>
    intro h
    simpa only [Multiset.map_cons, Multiset.sum_cons] using!
      (analyticAt_const.fun_div (analyticAt_const.fun_sub (analyticAt_id.fun_mul analyticAt_const))
        (h a (Multiset.mem_cons_self _ _))).fun_add
        (ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)))

theorem weighted_cauchy_moment_resolvent_disk
    (P Q : Multiset ℂ) (r σ : ℂ) {K : Set ℂ} (hK : IsCompact K)
    (μ : Measure ℂ) [IsFiniteMeasure μ] {M : ℝ} (hM : 0 < M)
    (hP : ∀ a ∈ P, ‖a‖ ≤ M) (hQ : ∀ a ∈ Q, ‖a‖ ≤ M)
    (hKM : ∀ a ∈ K, ‖a‖ ≤ M)
    (hmoment : ∀ n : ℕ,
      (P.map (fun a => a ^ n)).sum / r - (Q.map (fun a => a ^ n)).sum / r =
        σ * (∫ ζ in K, (X ^ n : ℂ[X]).derivative.derivative.eval ζ ∂μ))
    {w : ℂ} (hw : ‖w‖ < 1 / M) :
      (P.map (fun a => 1 / (1 - w * a))).sum / r -
        (Q.map (fun a => 1 / (1 - w * a))).sum / r =
          σ * (∫ ζ in K, 2 * w ^ 2 / (1 - w * ζ) ^ 3 ∂μ) := by
  let U : Set ℂ := ball 0 (1 / M)
  have hG : AnalyticOnNhd ℂ (fun w =>
      (P.map (fun a => 1 / (1 - w * a))).sum / r -
        (Q.map (fun a => 1 / (1 - w * a))).sum / r) U := by
    intro z hz
    have hz' : ‖z‖ < 1 / M := by simpa only [U, mem_ball, dist_zero_right] using hz
    exact ((analyticAt_multiset_geometric_away P
      (fun a ha => one_sub_mul_ne_zero_of_norm_bound hM hz' (hP a ha))).div_const (c := r)).sub
      ((analyticAt_multiset_geometric_away Q
        (fun a ha => one_sub_mul_ne_zero_of_norm_bound hM hz' (hQ a ha))).div_const (c := r))
  have hH : AnalyticOnNhd ℂ (fun w => σ *
      (∫ ζ in K, 2 * w ^ 2 / (1 - w * ζ) ^ 3 ∂μ)) U := by
    intro z hz
    have hz' : ‖z‖ < 1 / M := by simpa only [U, mem_ball, dist_zero_right] using hz
    apply (analyticAt_const (v := σ)).fun_mul
    apply analyticAt_integral_compact_joint
      (F := fun p : ℂ × ℂ => 2 * p.1 ^ 2 / (1 - p.1 * p.2) ^ 3) hK μ
    intro a ha
    exact (analyticAt_const.mul (analyticAt_fst.pow 2)).div
      ((analyticAt_const.sub (analyticAt_fst.mul analyticAt_snd)).pow 3)
      (pow_ne_zero _ (one_sub_mul_ne_zero_of_norm_bound hM hz' (hKM a ha)))
  exact hG.eqOn_of_preconnected_of_eventuallyEq hH (convex_ball 0 (1 / M)).isPreconnected
    (by simpa only [U, mem_ball, dist_self] using one_div_pos.mpr hM)
    (weighted_cauchy_moment_resolvent_germ P Q r σ hK μ hmoment)
    (by simpa only [U, mem_ball, dist_zero_right] using hw)

end
end CGLMPBounds.Hardy
