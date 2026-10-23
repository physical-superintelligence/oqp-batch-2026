module

public import CGLMPBounds.Hardy.UpperClusterNeighborhood
public import Mathlib.Analysis.Calculus.ParametricCircleIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section


/-!
# Holomorphy of the actual upper-cluster trace

The fixed contour from `UpperClusterNeighborhood` stays in the resolvent set
on a common neighborhood of the parameter. Joint analyticity of its actual
integrand gives a continuous parameter derivative. Compactness of the circle
then supplies a uniform local bound, so the parametric circle-integral theorem
applies. The final upper-half-plane theorem assumes only the source Hermitian
and invertibility hypotheses, with no chosen contour or derivative oracle.

This is the interior holomorphy step in the proof of Lemma C.3.
-/

open Complex Metric Set Filter MeasureTheory
open scoped Topology Interval Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

/-- The derivative of a joint function in its first, parameter coordinate. -/
def circleParameterDerivative (F : ℂ × ℂ → ℂ) (w ζ : ℂ) : ℂ :=
  fderiv ℂ F (w, ζ) (1, 0)

lemma continuousAt_circleParameterDerivative {F : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hF : AnalyticAt ℂ F p) :
    ContinuousAt (fun q : ℂ × ℂ => circleParameterDerivative F q.1 q.2) p := by
  have hd : ContDiffAt ℂ 1 F p := hF.contDiffAt
  change ContinuousAt (fun q : ℂ × ℂ => fderiv ℂ F q (1, 0)) p
  exact (hd.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const

lemma hasDerivAt_circleSlice {F : ℂ × ℂ → ℂ} {w ζ : ℂ}
    (hF : AnalyticAt ℂ F (w, ζ)) :
    HasDerivAt (fun v => F (v, ζ)) (circleParameterDerivative F w ζ) w := by
  have hd := hF.differentiableAt.hasFDerivAt.comp w
    (hasFDerivAt_prodMk_left (𝕜 := ℂ) w ζ)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, circleParameterDerivative] using hd.hasDerivAt

lemma continuousOn_circleSlice {F : ℂ × ℂ → ℂ} {w c : ℂ} {R : ℝ}
    (hF : ∀ ζ ∈ sphere c |R|, AnalyticAt ℂ F (w, ζ)) :
    ContinuousOn (fun ζ => F (w, ζ)) (sphere c |R|) := by
  intro ζ hζ
  exact ((hF ζ hζ).continuousAt.comp
    (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt

lemma continuousOn_circleParameterDerivative {F : ℂ × ℂ → ℂ} {w c : ℂ} {R : ℝ}
    (hF : ∀ ζ ∈ sphere c |R|, AnalyticAt ℂ F (w, ζ)) :
    ContinuousOn (circleParameterDerivative F w) (sphere c |R|) := by
  intro ζ hζ
  exact ((continuousAt_circleParameterDerivative (hF ζ hζ)).comp
    (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt

/-- Joint analyticity near a fixed compact circle gives an actual derivative
under the integral. The local derivative bound is proved here by compactness;
it is not an additional hypothesis. -/
theorem hasDerivAt_circleIntegral_of_joint_analytic
    {F : ℂ × ℂ → ℂ} {z c : ℂ} {R : ℝ}
    (hF : ∀ᶠ w in 𝓝 z, ∀ ζ ∈ sphere c |R|, AnalyticAt ℂ F (w, ζ)) :
    HasDerivAt (fun w => ∮ ζ in C(c, R), F (w, ζ))
      (∮ ζ in C(c, R), circleParameterDerivative F z ζ) z := by
  have hF0 : ∀ ζ ∈ sphere c |R|, AnalyticAt ℂ F (z, ζ) := hF.self_of_nhds
  have hD0 := continuousOn_circleParameterDerivative hF0
  obtain ⟨M, hM⟩ := (isCompact_sphere c |R|).exists_bound_of_continuousOn hD0
  have hbound : ∀ᶠ w in 𝓝 z,
      ∀ ζ ∈ sphere c |R|, ‖circleParameterDerivative F w ζ‖ ≤ M + 1 := by
    apply (isCompact_sphere c |R|).eventually_forall_of_forall_eventually
    intro ζ hζ
    have hc := (continuousAt_circleParameterDerivative (hF0 ζ hζ)).norm
    have hlt : ‖circleParameterDerivative F z ζ‖ < M + 1 :=
      (hM ζ hζ).trans_lt (lt_add_one M)
    exact (hc.eventually_lt continuousAt_const hlt).mono fun _ h => h.le
  let s : Set ℂ := {w | (∀ ζ ∈ sphere c |R|, AnalyticAt ℂ F (w, ζ)) ∧
    ∀ ζ ∈ sphere c |R|, ‖circleParameterDerivative F w ζ‖ ≤ M + 1}
  have hs : s ∈ 𝓝 z := hF.and hbound
  have hmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (fun θ : ℝ => F (w, circleMap c R θ))
        (volume.restrict (Ι 0 (2 * Real.pi))) := by
    filter_upwards [hF] with w hw
    exact ((continuousOn_circleSlice hw).comp_continuous
      (continuous_circleMap c R) (circleMap_mem_sphere' c R)).aestronglyMeasurable
  have hint : CircleIntegrable (fun ζ => F (z, ζ)) c R :=
    (continuousOn_circleSlice hF0).circleIntegrable'
  have hdmeas : AEStronglyMeasurable
      (fun θ : ℝ => circleParameterDerivative F z (circleMap c R θ))
        (volume.restrict (Ι 0 (2 * Real.pi))) :=
    (hD0.comp_continuous (continuous_circleMap c R)
      (circleMap_mem_sphere' c R)).aestronglyMeasurable
  have hd := hasDerivAt_circleIntegral_of_dominated_loc_of_deriv_le
    (F := fun w ζ => F (w, ζ)) (F' := circleParameterDerivative F)
    (bound := fun _ => M + 1) hs hmeas hint hdmeas
    (fun ζ hζ w hw => hw.2 ζ hζ) (circleIntegrable_const (M + 1) c R)
    (fun ζ hζ w hw => hasDerivAt_circleSlice (hw.1 ζ hζ))
  exact hd.2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- The first coordinate is the pencil parameter, the second the contour point. -/
def pencilTraceJoint (H Y : Matrix ι ι ℂ) (p : ℂ × ℂ) : ℂ :=
  pencilTraceIntegrand H Y p.2 p.1

set_option backward.isDefEq.respectTransparency false in
/-- Joint analyticity holds on the actual resolvent domain, without assumptions
on eigenvalue multiplicities or diagonalizability. -/
theorem analyticAt_pencilTraceJoint (H Y : Matrix ι ι ℂ) {p : ℂ × ℂ}
    (hp : p.2 ∉ spectrum ℂ (traceDensityPencil H Y p.1)) :
    AnalyticAt ℂ (pencilTraceJoint H Y) p := by
  have hL : AnalyticAt ℂ (fun q : ℂ × ℂ => traceDensityPencil H Y q.1) p :=
    (analyticAt_traceDensityPencil H Y p.1).comp analyticAt_fst
  have hscalar : AnalyticAt ℂ
      (fun q : ℂ × ℂ => algebraMap ℂ (Matrix ι ι ℂ) q.2) p := by
    convert! (analyticAt_snd (𝕜 := ℂ) (p := p)).smul
      (analyticAt_const (v := (1 : Matrix ι ι ℂ))) using 1 <;>
      simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply] <;>
      (funext q; rfl)
  have hu : IsUnit (algebraMap ℂ (Matrix ι ι ℂ) p.2 - traceDensityPencil H Y p.1) := by
    simpa only [spectrum.mem_iff, not_not] using hp
  have hinv : AnalyticAt ℂ Ring.inverse
      (algebraMap ℂ (Matrix ι ι ℂ) p.2 - traceDensityPencil H Y p.1) := by
    simpa only [hu.unit_spec] using analyticAt_inverse (𝕜 := ℂ) hu.unit
  have hres : AnalyticAt ℂ (fun q : ℂ × ℂ => pencilResolvent H Y q.2 q.1) p :=
    hinv.comp (f := fun q : ℂ × ℂ =>
      algebraMap ℂ (Matrix ι ι ℂ) q.2 - traceDensityPencil H Y q.1) (hscalar.sub hL)
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have ht : AnalyticAt ℂ
      (fun q : ℂ × ℂ => Matrix.trace
        (traceDensityPencil H Y q.1 * pencilResolvent H Y q.2 q.1)) p :=
    (tr.analyticAt _).comp (hL.mul hres)
  convert! ht.mul (analyticAt_const (v := (Fintype.card ι : ℂ)⁻¹)) using 1 <;>
    simp only [pencilTraceJoint, pencilTraceIntegrand, div_eq_mul_inv, Pi.mul_apply]

/-- Differentiation of the explicit source contour. Every analytic and uniform
bound premise of differentiation under the integral is discharged above. -/
theorem hasDerivAt_pencil_fixed_circle {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {z : ℂ} (hz : 0 < z.im) :
    let R := upperClusterRadius (traceDensityPencil H Y z).charpoly.roots
    HasDerivAt
      (fun w => ∮ ζ in C((R : ℂ) * Complex.I, R), pencilTraceIntegrand H Y ζ w)
      (∮ ζ in C((R : ℂ) * Complex.I, R),
        circleParameterDerivative (pencilTraceJoint H Y) z ζ) z := by
  let R := upperClusterRadius (traceDensityPencil H Y z).charpoly.roots
  apply hasDerivAt_circleIntegral_of_joint_analytic (F := pencilTraceJoint H Y)
  have hR : 0 ≤ R := (upperClusterRadius_pos _).le
  filter_upwards [eventually_pencil_fixed_circle_resolvent hH hY hdet hz] with w hw
  intro ζ hζ
  exact analyticAt_pencilTraceJoint H Y (hw ζ (by
    simpa only [abs_of_pos (upperClusterRadius_pos _)] using hζ))

/-- The source upper-cluster trace is complex differentiable throughout the
upper half-plane. The contour is derived from the actual characteristic roots. -/
theorem differentiableAt_pencil_upperClusterTrace {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (fun w => upperClusterTrace (traceDensityPencil H Y w)) z := by
  have hd := (hasDerivAt_pencil_fixed_circle hH hY hdet hz).differentiableAt.div_const
    (2 * Real.pi * Complex.I : ℂ)
  exact hd.congr_of_eventuallyEq
    (pencil_upperClusterTrace_eventuallyEq_fixed_circle hH hY hdet hz)

/-- Interior holomorphy asserted in the proof of source Lemma C.3, for the
literal normalized multiset sum of upper-half-plane eigenvalues. -/
theorem analyticOnNhd_pencil_upperClusterTrace {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) :
    AnalyticOnNhd ℂ (fun z => upperClusterTrace (traceDensityPencil H Y z))
      {z : ℂ | 0 < z.im} := by
  have hd : DifferentiableOn ℂ (fun z => upperClusterTrace (traceDensityPencil H Y z))
      {z : ℂ | 0 < z.im} :=
    fun z hz => (differentiableAt_pencil_upperClusterTrace hH hY hdet hz).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_im)

end
end CGLMPBounds.Hardy
