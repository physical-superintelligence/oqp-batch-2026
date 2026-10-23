module

public import CGLMPBounds.Hardy.HolomorphicCircleTrace
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section


/-! The genuine second-derivative Cauchy formula at arbitrary interior
points, and finite compact-measure interchange with a fixed circle.
Neither interchange nor a holomorphic moment extension is assumed. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Complex Set Metric Filter MeasureTheory
open scoped Topology

theorem circleIntegral_second_cauchy {f : ℂ → ℂ} {c a : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (ha : a ∈ ball c R) :
    (∮ ζ in C(c, R), 2 * f ζ / (ζ - a) ^ 3) =
      (2 * Real.pi * Complex.I : ℂ) * iteratedDeriv 2 f a := by
  let F₁ : ℂ → ℂ := fun w => ∮ ζ in C(c, R), (ζ - w)⁻¹ • f ζ
  let F₂ : ℂ → ℂ := fun w => ∮ ζ in C(c, R), (ζ - w) ^ (-2 : ℤ) • f ζ
  have hfi : CircleIntegrable f c R :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR
  have hsep {w : ℂ} (hw : w ∈ ball c R) : w ∉ sphere c |R| := by
    rw [abs_of_nonneg hR]
    intro hs
    exact (Metric.mem_ball.mp hw).ne (Metric.mem_sphere.mp hs)
  have hfirst : ∀ w ∈ ball c R, F₂ w =
      (2 * Real.pi * Complex.I : ℂ) * deriv f w := by
    intro w hw
    have he : F₁ =ᶠ[𝓝 w] (fun z => (2 * Real.pi * Complex.I : ℂ) * f z) := by
      filter_upwards [isOpen_ball.mem_nhds hw] with z hz
      exact Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        Set.countable_empty hz hf.continuousOn
        (fun v hv => (hf v (ball_subset_closedBall hv.1)).differentiableAt)
    have hd := Complex.hasDerivAt_circleIntegral_sub_inv_smul hfi (hsep hw)
    calc
      F₂ w = deriv F₁ w := hd.deriv.symm
      _ = deriv (fun z => (2 * Real.pi * Complex.I : ℂ) * f z) w := he.deriv_eq
      _ = (2 * Real.pi * Complex.I : ℂ) * deriv f w :=
        ((hf w (ball_subset_closedBall hw)).differentiableAt.hasDerivAt.const_mul _).deriv
  have he : F₂ =ᶠ[𝓝 a] (fun w => (2 * Real.pi * Complex.I : ℂ) * deriv f w) := by
    filter_upwards [isOpen_ball.mem_nhds ha] with w hw
    exact hfirst w hw
  have hd := Complex.hasDerivAt_circleIntegral_sub_zpow_smul (n := (-2 : ℤ)) hfi (hsep ha)
  have heq := he.deriv_eq
  rw [hd.deriv] at heq
  have hfd : DifferentiableAt ℂ (deriv f) a :=
    ((hf a (ball_subset_closedBall ha)).deriv).differentiableAt
  rw [(hfd.hasDerivAt.const_mul (2 * Real.pi * Complex.I : ℂ)).deriv] at heq
  simpa only [F₂, show (-2 : ℤ) - 1 = -3 by norm_num,
    Int.cast_neg, Int.cast_ofNat, neg_neg, zpow_neg, zpow_ofNat, smul_eq_mul,
    ← circleIntegral.integral_const_mul, iteratedDeriv_succ, iteratedDeriv_zero,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using heq

theorem circleIntegral_integral_compact_swap
    {K : Set ℂ} (hK : IsCompact K) (μ : Measure ℂ) [IsFiniteMeasure μ]
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) {F : ℂ × ℂ → ℂ}
    (hF : ContinuousOn F (sphere c R ×ˢ K)) :
    (∮ ζ in C(c, R), ∫ a in K, F (ζ, a) ∂μ) =
      ∫ a in K, (∮ ζ in C(c, R), F (ζ, a)) ∂μ := by
  let G : ℝ × ℂ → ℂ := fun p =>
    deriv (circleMap c R) p.1 • F (circleMap c R p.1, p.2)
  have hG : ContinuousOn G (Icc (0 : ℝ) (2 * Real.pi) ×ˢ K) := by
    change ContinuousOn (fun p : ℝ × ℂ =>
      deriv (circleMap c R) p.1 • F (circleMap c R p.1, p.2)) _
    apply ContinuousOn.fun_smul
    · simp only [deriv_circleMap]
      fun_prop
    · apply hF.comp (by fun_prop)
      intro p hp
      exact ⟨circleMap_mem_sphere c hR p.1, hp.2⟩
  have hi : Integrable G ((volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))).prod
      (μ.restrict K)) := by
    rw [uIoc_of_le (by positivity), restrict_Ioc_eq_restrict_Icc, Measure.prod_restrict]
    exact hG.integrableOn_compact (isCompact_Icc.prod hK)
  simp only [circleIntegral]
  have hs := intervalIntegral_integral_swap
    (f := fun θ a => deriv (circleMap c R) θ • F (circleMap c R θ, a)) hi
  convert hs using 1
  · apply intervalIntegral.integral_congr
    intro θ _
    exact (integral_smul _ _).symm

end
end CGLMPBounds.Hardy
