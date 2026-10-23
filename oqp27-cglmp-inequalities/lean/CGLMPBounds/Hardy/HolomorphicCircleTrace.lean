module

public import CGLMPBounds.Defs.HolomorphicPinching
public import CGLMPBounds.Hardy.SchwarzContourCoefficients

@[expose] public section


/-! Actual local circle functional calculus for a scalar holomorphic trace.
The circle selects roots with their full algebraic multiplicities, so no
normality or diagonalizability is needed. These local formulas are used for
analyticity across collisions of characteristic roots in C.5 and C.6. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Complex Matrix Set Metric Filter
open scoped Topology Classical Matrix.Norms.Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma holomorphicRootFraction_circleIntegrable {f : ℂ → ℂ} {c a : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (ha : a ∉ sphere c R) :
    CircleIntegrable (fun ζ : ℂ => f ζ / (ζ - a)) c R := by
  apply ContinuousOn.circleIntegrable hR
  exact (hf.continuousOn.mono sphere_subset_closedBall).div
    (continuousOn_id.sub continuousOn_const)
    (fun ζ hζ => sub_ne_zero.mpr (ne_of_mem_of_not_mem hζ ha))

lemma circleIntegral_holomorphicRootFraction {f : ℂ → ℂ} {c a : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (ha : a ∉ sphere c R) :
    (∮ ζ in C(c, R), f ζ / (ζ - a)) =
      (2 * Real.pi * Complex.I : ℂ) * (if a ∈ ball c R then f a else 0) := by
  by_cases hin : a ∈ ball c R
  · rw [if_pos hin]
    exact Complex.circleIntegral_div_sub_of_differentiable_on_off_countable
      Set.countable_empty hin hf.continuousOn
      (fun ζ hζ => (hf ζ (ball_subset_closedBall hζ.1)).differentiableAt)
  · rw [if_neg hin, mul_zero]
    have hout : a ∉ closedBall c R := by
      intro hc
      exact ha (Metric.mem_sphere.mpr (le_antisymm hc (le_of_not_gt hin)))
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      hR (s := (∅ : Set ℂ)) Set.countable_empty
    · exact hf.continuousOn.div (continuousOn_id.sub continuousOn_const)
        (fun ζ hζ => sub_ne_zero.mpr (ne_of_mem_of_not_mem hζ hout))
    · intro ζ hζ
      exact ((hf ζ (ball_subset_closedBall hζ.1)).differentiableAt).div
        (differentiableAt_id.sub_const a)
        (sub_ne_zero.mpr (ne_of_mem_of_not_mem (ball_subset_closedBall hζ.1) hout))

lemma holomorphicRootFractionSum_circleIntegrable (s : Multiset ℂ)
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hsep : ∀ a ∈ s, a ∉ sphere c R) :
    CircleIntegrable (fun ζ => (s.map (fun a => f ζ / (ζ - a))).sum) c R := by
  revert hsep
  induction s using Multiset.induction_on with
  | empty => intro _; simpa using circleIntegrable_const (0 : ℂ) c R
  | @cons a s ih =>
    intro hsep
    have hadd :=
      (holomorphicRootFraction_circleIntegrable hR hf (hsep a (Multiset.mem_cons_self _ _))).add
        (ih (fun b hb => hsep b (Multiset.mem_cons_of_mem hb)))
    change CircleIntegrable
      (fun ζ => f ζ / (ζ - a) + (s.map (fun b => f ζ / (ζ - b))).sum) c R at hadd
    simpa only [Multiset.map_cons, Multiset.sum_cons] using hadd

lemma circleIntegral_holomorphicRootFractionSum (s : Multiset ℂ)
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hsep : ∀ a ∈ s, a ∉ sphere c R) :
    (∮ ζ in C(c, R), (s.map (fun a => f ζ / (ζ - a))).sum) =
      (2 * Real.pi * Complex.I : ℂ) *
        (s.map (fun a => if a ∈ ball c R then f a else 0)).sum := by
  revert hsep
  induction s using Multiset.induction_on with
  | empty => intro _; simp [circleIntegral]
  | @cons a s ih =>
    intro hsep
    have ha := hsep a (Multiset.mem_cons_self _ _)
    have hs : ∀ b ∈ s, b ∉ sphere c R := fun b hb => hsep b (Multiset.mem_cons_of_mem hb)
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [circleIntegral.integral_add (holomorphicRootFraction_circleIntegrable hR hf ha)
      (holomorphicRootFractionSum_circleIntegrable s hR hf hs),
      circleIntegral_holomorphicRootFraction hR hf ha, ih hs]
    ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem circleIntegral_holomorphic_resolvent_trace (A : Matrix ι ι ℂ)
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hsep : ∀ a ∈ A.charpoly.roots, a ∉ sphere c R) :
    (∮ ζ in C(c, R), f ζ * Matrix.trace (resolvent A ζ)) /
        (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) =
      (A.charpoly.roots.map (fun a => if a ∈ ball c R then f a else 0)).sum /
        (Fintype.card ι : ℂ) := by
  have he : (∮ ζ in C(c, R), f ζ * Matrix.trace (resolvent A ζ)) =
      ∮ ζ in C(c, R), (A.charpoly.roots.map (fun a => f ζ / (ζ - a))).sum := by
    apply circleIntegral.integral_congr hR
    intro ζ hζ
    change f ζ * Matrix.trace (resolvent A ζ) =
      (A.charpoly.roots.map (fun a => f ζ / (ζ - a))).sum
    rw [trace_resolvent_eq_root_sum A
      (circle_not_mem_spectrum_of_root_separation A hsep hζ),
      ← Multiset.sum_map_mul_left]
    simp only [mul_one_div]
  rw [he, circleIntegral_holomorphicRootFractionSum A.charpoly.roots hR hf hsep,
    mul_div_cancel_left₀ _ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])]

lemma analyticAt_holomorphic_resolvent_trace_joint
    {M : ℂ → Matrix ι ι ℂ} {f : ℂ → ℂ} {z ζ : ℂ}
    (hM : AnalyticAt ℂ M z) (hf : AnalyticAt ℂ f ζ)
    (hζ : ζ ∉ spectrum ℂ (M z)) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => f p.2 * Matrix.trace (resolvent (M p.1) p.2)) (z, ζ) := by
  have harg : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      algebraMap ℂ (Matrix ι ι ℂ) p.2 - M p.1) (z, ζ) := by
    simp only [Algebra.algebraMap_eq_smul_one]
    exact (analyticAt_snd.smul analyticAt_const).sub (hM.comp analyticAt_fst)
  have hu : IsUnit (algebraMap ℂ (Matrix ι ι ℂ) ζ - M z) :=
    spectrum.notMem_iff.mp hζ
  have hi : AnalyticAt ℂ Ring.inverse (algebraMap ℂ (Matrix ι ι ℂ) ζ - M z) := by
    simpa only [hu.unit_spec] using analyticAt_inverse (𝕜 := ℂ) hu.unit
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have hres : AnalyticAt ℂ
      (fun p : ℂ × ℂ => resolvent (M p.1) p.2) (z, ζ) :=
    hi.comp (f := fun p : ℂ × ℂ => algebraMap ℂ (Matrix ι ι ℂ) p.2 - M p.1) harg
  exact (hf.comp analyticAt_snd).mul ((tr.analyticAt _).comp hres)

theorem analyticAt_holomorphic_circle_trace
    {M : ℂ → Matrix ι ι ℂ} {f : ℂ → ℂ} {z c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hM : AnalyticAt ℂ M z)
    (hf : ∀ ζ ∈ sphere c R, AnalyticAt ℂ f ζ)
    (hsep : ∀ ζ ∈ sphere c R, ζ ∉ spectrum ℂ (M z)) :
    AnalyticAt ℂ (fun w => (∮ ζ in C(c, R), f ζ * Matrix.trace (resolvent (M w) ζ)) /
      (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ)) z := by
  have hF : ∀ ζ ∈ sphere c R, AnalyticAt ℂ
      (fun p : ℂ × ℂ => f p.2 * Matrix.trace (resolvent (M p.1) p.2)) (z, ζ) :=
    fun ζ hζ => analyticAt_holomorphic_resolvent_trace_joint hM (hf ζ hζ) (hsep ζ hζ)
  have he : ∀ᶠ w in 𝓝 z, ∀ ζ ∈ sphere c R, AnalyticAt ℂ
      (fun p : ℂ × ℂ => f p.2 * Matrix.trace (resolvent (M p.1) p.2)) (w, ζ) :=
    (isCompact_sphere c R).eventually_forall_of_forall_eventually
      (fun ζ hζ => (hF ζ hζ).eventually_analyticAt)
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [he.eventually_nhds] with w hw
  have hd := hasDerivAt_circleIntegral_of_joint_analytic
    (F := fun p : ℂ × ℂ => f p.2 * Matrix.trace (resolvent (M p.1) p.2))
    (z := w) (c := c) (R := R)
    (by simpa only [abs_of_nonneg hR] using hw)
  exact (hd.differentiableAt.div_const _).div_const _

end
end CGLMPBounds.Hardy
