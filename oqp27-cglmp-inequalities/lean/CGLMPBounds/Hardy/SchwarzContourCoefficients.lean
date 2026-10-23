module

public import CGLMPBounds.Hardy.UpperClusterAnalytic
public import CGLMPBounds.Hardy.SchwarzResolventSeries
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section


/-!
# All-order coefficient interchange on actual fixed resolvent circles

Joint analyticity near a compact circle supplies each parameter derivative
under the contour integral. Iteration is carried out using actual Frechet
derivatives, then identified with ordinary slice derivatives. In the affine
matrix application all analytic premises follow from actual spectral
avoidance on the fixed base circle, not from a coefficient oracle.

This is the remaining local coefficient-interchange ingredient of the p.9
C.7 argument. Cluster selection and contour inversion remain separate.
-/

open Complex Filter Set Metric
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

def jointCircleDerivative (F : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  circleParameterDerivative F p.1 p.2

def jointCircleIteratedDerivative : ℕ → (ℂ × ℂ → ℂ) → (ℂ × ℂ → ℂ)
  | 0, F => F
  | n + 1, F => jointCircleIteratedDerivative n (jointCircleDerivative F)

lemma analyticAt_jointCircleDerivative {F : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hF : AnalyticAt ℂ F p) : AnalyticAt ℂ (jointCircleDerivative F) p := by
  let ev : ((ℂ × ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1, 0)
  exact (ev.analyticAt _).comp hF.fderiv

lemma iteratedDeriv_circleSlice_eq (n : ℕ) {F : ℂ × ℂ → ℂ} {w ζ : ℂ}
    (hF : AnalyticAt ℂ F (w, ζ)) :
    iteratedDeriv n (fun v : ℂ => F (v, ζ)) w = jointCircleIteratedDerivative n F (w, ζ) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hc : Continuous (fun v : ℂ => (v, ζ)) := by fun_prop
    have he : deriv (fun v : ℂ => F (v, ζ)) =ᶠ[𝓝 w]
        (fun v : ℂ => jointCircleDerivative F (v, ζ)) := by
      filter_upwards [(hc.tendsto w).eventually hF.eventually_analyticAt] with v hv
      exact (hasDerivAt_circleSlice hv).deriv
    rw [he.iteratedDeriv_eq n]
    exact ih (analyticAt_jointCircleDerivative hF)

lemma iteratedDeriv_circleIntegral_joint (n : ℕ) {F : ℂ × ℂ → ℂ} {z c : ℂ} {R : ℝ}
    (hF : ∀ᶠ w in 𝓝 z, ∀ ζ ∈ sphere c |R|, AnalyticAt ℂ F (w, ζ)) :
    iteratedDeriv n (fun w => ∮ ζ in C(c, R), F (w, ζ)) z =
      ∮ ζ in C(c, R), jointCircleIteratedDerivative n F (z, ζ) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have he : deriv (fun w => ∮ ζ in C(c, R), F (w, ζ)) =ᶠ[𝓝 z]
        (fun w => ∮ ζ in C(c, R), jointCircleDerivative F (w, ζ)) := by
      filter_upwards [hF.eventually_nhds] with w hw
      exact (hasDerivAt_circleIntegral_of_joint_analytic hw).deriv
    rw [he.iteratedDeriv_eq n]
    exact ih (hF.mono fun w hw ζ hζ => analyticAt_jointCircleDerivative (hw ζ hζ))

/-- Actual all-order differentiation under a fixed circle integral.
Only joint analyticity at points of the base compact circle is required. -/
theorem iteratedDeriv_circleIntegral_of_joint_analytic (n : ℕ)
    {F : ℂ × ℂ → ℂ} {z c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hF : ∀ ζ ∈ sphere c R, AnalyticAt ℂ F (z, ζ)) :
    iteratedDeriv n (fun w => ∮ ζ in C(c, R), F (w, ζ)) z =
      ∮ ζ in C(c, R), iteratedDeriv n (fun w => F (w, ζ)) z := by
  have he : ∀ᶠ w in 𝓝 z, ∀ ζ ∈ sphere c R, AnalyticAt ℂ F (w, ζ) :=
    (isCompact_sphere c R).eventually_forall_of_forall_eventually
      (fun ζ hζ => (hF ζ hζ).eventually_analyticAt)
  rw [iteratedDeriv_circleIntegral_joint n (by simpa only [abs_of_nonneg hR] using he)]
  apply circleIntegral.integral_congr hR
  intro ζ hζ
  exact (iteratedDeriv_circleSlice_eq n (hF ζ hζ)).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option backward.isDefEq.respectTransparency false in
lemma analyticAt_affine_resolvent_trace_joint (H Y : Matrix ι ι ℂ) (m : ℕ) {p : ℂ × ℂ}
    (hp : p.2 ∉ spectrum ℂ (H + p.1 • Y)) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => q.2 ^ m * Matrix.trace (resolvent (H + q.1 • Y) q.2)) p := by
  have harg : AnalyticAt ℂ (fun q : ℂ × ℂ =>
      algebraMap ℂ (Matrix ι ι ℂ) q.2 - (H + q.1 • Y)) p := by
    have hscalar : AnalyticAt ℂ
        (fun q : ℂ × ℂ => algebraMap ℂ (Matrix ι ι ℂ) q.2) p := by
      convert! (analyticAt_snd (𝕜 := ℂ) (p := p)).smul
        (analyticAt_const (v := (1 : Matrix ι ι ℂ))) using 1 <;>
        simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply] <;>
        (funext q; rfl)
    have hlinear : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1 • Y) p := by
      convert! (analyticAt_fst (𝕜 := ℂ) (p := p)).smul
        (analyticAt_const (v := Y)) using 1 <;>
        (funext q; rfl)
    exact hscalar.sub (analyticAt_const.add hlinear)
  have hu : IsUnit (algebraMap ℂ (Matrix ι ι ℂ) p.2 - (H + p.1 • Y)) := by
    simpa only [spectrum.mem_iff, not_not] using hp
  have hinv : AnalyticAt ℂ Ring.inverse
      (algebraMap ℂ (Matrix ι ι ℂ) p.2 - (H + p.1 • Y)) := by
    simpa only [hu.unit_spec] using analyticAt_inverse (𝕜 := ℂ) hu.unit
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have hres : AnalyticAt ℂ
      (fun q : ℂ × ℂ => resolvent (H + q.1 • Y) q.2) p :=
    hinv.comp (f := fun q : ℂ × ℂ =>
      algebraMap ℂ (Matrix ι ι ℂ) q.2 - (H + q.1 • Y)) harg
  exact (analyticAt_snd.pow m).mul ((tr.analyticAt _).comp hres)

/-- Literal Taylor coefficient of an actual fixed-circle affine resolvent
power trace. Every local joint-analytic premise is discharged by hsep. -/
theorem circleIntegral_affine_resolvent_taylor_coefficient
    (H Y : Matrix ι ι ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hsep : ∀ ζ ∈ sphere c R, ζ ∉ spectrum ℂ H) (m n : ℕ) :
    iteratedDeriv n (fun t : ℂ => ∮ ζ in C(c, R),
      ζ ^ m * Matrix.trace (resolvent (H + t • Y) ζ)) 0 / (n.factorial : ℂ) =
      ∮ ζ in C(c, R), ζ ^ m * Matrix.trace ((resolvent H ζ * Y) ^ n * resolvent H ζ) := by
  have hd := iteratedDeriv_circleIntegral_of_joint_analytic n hR
    (F := fun p : ℂ × ℂ => p.2 ^ m * Matrix.trace (resolvent (H + p.1 • Y) p.2))
    (z := 0) (by
      intro ζ hζ
      exact analyticAt_affine_resolvent_trace_joint H Y m (by simpa using hsep ζ hζ))
  rw [hd]
  have he : (∮ ζ in C(c, R),
      iteratedDeriv n (fun t : ℂ => ζ ^ m * Matrix.trace (resolvent (H + t • Y) ζ)) 0) /
        (n.factorial : ℂ) =
      ∮ ζ in C(c, R),
        iteratedDeriv n (fun t : ℂ => ζ ^ m * Matrix.trace (resolvent (H + t • Y) ζ)) 0 /
          (n.factorial : ℂ) := by
    simpa only [div_eq_mul_inv, smul_eq_mul] using
      (circleIntegral.integral_smul_const
        (fun ζ => iteratedDeriv n
          (fun t : ℂ => ζ ^ m * Matrix.trace (resolvent (H + t • Y) ζ)) 0)
        ((n.factorial : ℂ)⁻¹) c R).symm
  rw [he]
  apply circleIntegral.integral_congr hR
  intro ζ hζ
  have hcoeff := trace_affine_resolvent_taylor_coefficient H Y (hsep ζ hζ) n
  change iteratedDeriv n (fun t : ℂ => ζ ^ m * Matrix.trace (resolvent (H + t • Y) ζ)) 0 /
    (n.factorial : ℂ) = ζ ^ m * Matrix.trace ((resolvent H ζ * Y) ^ n * resolvent H ζ)
  rw [show (fun t : ℂ => ζ ^ m * Matrix.trace (resolvent (H + t • Y) ζ)) =
      ζ ^ m • (fun t : ℂ => Matrix.trace (resolvent (H + t • Y) ζ)) by rfl,
    iteratedDeriv_const_smul_field]
  simpa only [Pi.smul_apply, smul_eq_mul, mul_div_assoc] using congrArg (fun u : ℂ => ζ ^ m * u) hcoeff

end
end CGLMPBounds.Hardy
