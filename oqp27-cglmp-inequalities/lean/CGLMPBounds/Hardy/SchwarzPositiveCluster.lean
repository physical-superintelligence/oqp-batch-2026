module

public import CGLMPBounds.Hardy.SchwarzCirclePowerTrace
public import CGLMPBounds.Hardy.SchwarzExteriorContour
public import CGLMPBounds.Hardy.SchwarzContourCoefficients

@[expose] public section


/-! A fixed, genuine positive-cluster contour near an invertible Hermitian
base H. Spectral upper hemicontinuity supplies the neighborhood; for real t,
Hermiticity of H+tY then identifies its selected contour power trace with the
actual positive-part trace. No desired cluster equality is a hypothesis.
This is one of the remaining substantive bridges in C.7. -/

open Complex Metric Set Filter
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

lemma dist_sq_positive_real_center (a : ℂ) (T : ℝ) :
    dist a (T : ℂ) ^ 2 = ‖a‖ ^ 2 + T ^ 2 - 2 * T * a.re := by
  rw [dist_eq_norm, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  ring

/-- The same finite radius formula as the negative circle, reflected into
the right half-plane. The root count retains multiplicity elsewhere. -/
lemma positiveClusterRadius_separates (s : Multiset ℂ)
    (haxis : ∀ a ∈ s, a.re ≠ 0) {a : ℂ} (ha : a ∈ s) :
    a ∉ sphere (negativeClusterRadius s : ℂ) (negativeClusterRadius s) ∧
      (a ∈ ball (negativeClusterRadius s : ℂ) (negativeClusterRadius s) ↔ 0 < a.re) := by
  have hT := negativeClusterRadius_pos s
  have hd := dist_sq_positive_real_center a (negativeClusterRadius s)
  by_cases hp : 0 < a.re
  · have hratio := negativeClusterRadius_gt_ratio s ha
    rw [abs_of_pos hp] at hratio
    have hmul := (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hp)).1 hratio
    have hlt : dist a (negativeClusterRadius s : ℂ) < negativeClusterRadius s := by
      apply (sq_lt_sq₀ dist_nonneg hT.le).1
      nlinarith
    refine ⟨?_, ⟨fun _ => hp, fun _ => hlt⟩⟩
    intro hs
    have he := Metric.mem_sphere.mp hs
    linarith
  · have hn : a.re < 0 := lt_of_le_of_ne (le_of_not_gt hp) (haxis a ha)
    have hprod : negativeClusterRadius s * a.re < 0 := mul_neg_of_pos_of_neg hT hn
    have hgt : negativeClusterRadius s < dist a (negativeClusterRadius s : ℂ) := by
      apply (sq_lt_sq₀ hT.le dist_nonneg).1
      nlinarith [sq_nonneg ‖a‖]
    refine ⟨?_, ⟨?_, fun h => False.elim (hp h)⟩⟩
    · intro hs
      have he := Metric.mem_sphere.mp hs
      linarith
    · intro hb
      have hlt : dist a (negativeClusterRadius s : ℂ) < negativeClusterRadius s := hb
      linarith

lemma positive_circle_ball_re_pos {T : ℝ} {a : ℂ}
    (ha : a ∈ ball (T : ℂ) T) : 0 < a.re := by
  have hnorm : ‖a - (T : ℂ)‖ < T := by
    simpa only [Metric.mem_ball, dist_eq_norm] using ha
  have hr := Complex.abs_re_le_norm (a - (T : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  linarith [neg_le_abs (a.re - T)]

lemma positive_circle_closedBall_re_nonneg {T : ℝ} {a : ℂ}
    (ha : a ∈ closedBall (T : ℂ) T) : 0 ≤ a.re := by
  have hnorm : ‖a - (T : ℂ)‖ ≤ T := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using ha
  have hr := Complex.abs_re_le_norm (a - (T : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  linarith [neg_le_abs (a.re - T)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma hermitian_root_re_ne_zero {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hdet : IsUnit H.det)
    {a : ℂ} (ha : a ∈ H.charpoly.roots) : a.re ≠ 0 := by
  have him : a.im = 0 := by
    have hr := ha
    rw [hH.roots_charpoly_eq_eigenvalues] at hr
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hr
    simp
  have hs : a ∈ spectrum ℂ H :=
    Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha)
  intro hre
  have he : a = 0 := Complex.ext hre him
  exact (spectrum.zero_notMem ℂ ((Matrix.isUnit_iff_isUnit_det H).mpr hdet)) (he ▸ hs)

/-- A single explicit contour encloses the positive cluster for every nearby
complex perturbation. Only the base must be Hermitian and invertible. -/
theorem eventually_affine_positive_circle_separates {H : Matrix ι ι ℂ}
    (Y : Matrix ι ι ℂ) (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    let R := negativeClusterRadius H.charpoly.roots
    ∀ᶠ t in 𝓝 (0 : ℂ), ∀ a ∈ (H + t • Y).charpoly.roots,
      a ∉ sphere (R : ℂ) R ∧ (a ∈ ball (R : ℂ) R ↔ 0 < a.re) := by
  let R := negativeClusterRadius H.charpoly.roots
  let U : Set ℂ := ball (R : ℂ) R ∪ {a : ℂ | a.re < 0}
  have hU : IsOpen U := isOpen_ball.union (isOpen_lt Complex.continuous_re continuous_const)
  have hsub : spectrum ℂ (H + (0 : ℂ) • Y) ⊆ U := by
    simp only [zero_smul, add_zero]
    intro a ha
    have hr : a ∈ H.charpoly.roots :=
      (Polynomial.mem_roots H.charpoly_monic.ne_zero).2
        (Matrix.mem_spectrum_iff_isRoot_charpoly.mp ha)
    by_cases hp : 0 < a.re
    · exact Or.inl ((positiveClusterRadius_separates _
        (fun b hb => hermitian_root_re_ne_zero hH hdet hb) hr).2.mpr hp)
    · exact Or.inr (lt_of_le_of_ne (le_of_not_gt hp) (hermitian_root_re_ne_zero hH hdet hr))
  have hcont : ContinuousAt (fun t : ℂ => H + t • Y) 0 := by fun_prop
  have hhemi : UpperHemicontinuousAt (fun t : ℂ => spectrum ℂ (H + t • Y)) 0 :=
    ((upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).upperHemicontinuousAt
      (H + (0 : ℂ) • Y)).comp (g := fun t : ℂ => H + t • Y) hcont
  filter_upwards [hhemi.forall_isOpen U hU hsub] with t ht
  intro a ha
  have hau : a ∈ U := ht
    (Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha))
  rcases hau with hin | hleft
  · refine ⟨?_, ⟨fun _ => positive_circle_ball_re_pos hin, fun _ => hin⟩⟩
    intro hs
    have hdlt : dist a (R : ℂ) < R := hin
    have hdeq := Metric.mem_sphere.mp hs
    linarith
  · have hout : a ∉ closedBall (R : ℂ) R := by
      intro hc
      exact (not_lt_of_ge (positive_circle_closedBall_re_nonneg hc)) hleft
    refine ⟨fun hs => hout (sphere_subset_closedBall hs), ⟨?_, ?_⟩⟩
    · intro hb
      exact False.elim (hout (ball_subset_closedBall hb))
    · intro hp
      exact False.elim ((not_lt_of_ge hp.le) hleft)

/-- The source positive-part functional is locally represented by an actual
fixed complex contour, with no spectral-selection oracle as a hypothesis. -/
theorem positiveTracePower_eventuallyEq_circlePowerTrace {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {m : ℕ} (hm : 0 < m) :
    let R := negativeClusterRadius H.charpoly.roots
    (fun t : ℝ => (positiveTracePower (H + (t : ℂ) • Y) m : ℂ)) =ᶠ[𝓝 0]
      (fun t : ℝ => circlePowerTrace (H + (t : ℂ) • Y) m (R : ℂ) R) := by
  have hc : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  filter_upwards [hc.eventually (eventually_affine_positive_circle_separates Y hH hdet)]
    with t ht
  have hA : (H + (t : ℂ) • Y).IsHermitian := hH.add (hY.smul (by simp [IsSelfAdjoint]))
  exact (circlePowerTrace_eq_positiveTracePower hA hm (negativeClusterRadius_pos _).le
    (fun a ha => (ht a ha).1) (fun a ha => (ht a ha).2)).symm

/-- The actual fixed positive-cluster power trace is analytic at the base.
This is the analyticity needed for its subsequent Taylor coefficient. -/
theorem analyticAt_affine_positive_circlePowerTrace {H : Matrix ι ι ℂ}
    (Y : Matrix ι ι ℂ) (hH : H.IsHermitian) (hdet : IsUnit H.det) (m : ℕ) :
    let R := negativeClusterRadius H.charpoly.roots
    AnalyticAt ℂ (fun t : ℂ => circlePowerTrace (H + t • Y) m (R : ℂ) R) 0 := by
  let R := negativeClusterRadius H.charpoly.roots
  have hR : 0 ≤ R := (negativeClusterRadius_pos _).le
  have hF : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ ζ ∈ sphere (R : ℂ) |R|,
      AnalyticAt ℂ (fun p : ℂ × ℂ =>
        p.2 ^ m * Matrix.trace (resolvent (H + p.1 • Y) p.2)) (t, ζ) := by
    filter_upwards [eventually_affine_positive_circle_separates Y hH hdet] with t ht
    intro ζ hζ
    apply analyticAt_affine_resolvent_trace_joint
    apply circle_not_mem_spectrum_of_root_separation (H + t • Y)
      (fun a ha => (ht a ha).1)
    simpa only [abs_of_nonneg hR] using hζ
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [hF.eventually_nhds] with t ht
  have hd := (hasDerivAt_circleIntegral_of_joint_analytic ht).differentiableAt
  exact (hd.div_const (2 * Real.pi * Complex.I : ℂ)).div_const (Fintype.card ι : ℂ)

end
end CGLMPBounds.Hardy
