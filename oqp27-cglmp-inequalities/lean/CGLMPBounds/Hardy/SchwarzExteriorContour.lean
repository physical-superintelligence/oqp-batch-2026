module

public import CGLMPBounds.Defs.HardyExterior
public import CGLMPBounds.Hardy.UpperClusterAnalytic

@[expose] public section


/-!
# The actual exterior negative-cluster contour of Lemma C.3

For `K(w) = H⁻¹ (I - wY)`, define the source function `q` by a fixed
normalized trace-resolvent circle integral. The circle is explicitly determined
by the characteristic roots of `H⁻¹`; at zero it selects precisely its negative
eigenvalues, with algebraic multiplicities. Spectral upper hemicontinuity keeps
this same contour in the resolvent set near zero, and differentiation under the
integral proves actual complex analyticity there.

This is the exterior construction preceding (C.8), supplement p. 8. It does not
yet prove `g(z) = -z*q(1/z)`, real Taylor coefficients, Schwarz reflection or the
slit Cauchy formula. No one of those statements is assumed here.
-/

open Complex Metric Set Filter
open scoped Topology Interval Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

lemma negativeClusterRadius_pos (s : Multiset ℂ) : 0 < negativeClusterRadius s := by
  classical
  have hs : 0 ≤ ∑ a ∈ s.toFinset, ‖a‖ ^ 2 / (2 * |a.re|) := by
    apply Finset.sum_nonneg
    intro a _
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))
  unfold negativeClusterRadius
  linarith

lemma negativeClusterRadius_gt_ratio (s : Multiset ℂ) {a : ℂ} (ha : a ∈ s) :
    ‖a‖ ^ 2 / (2 * |a.re|) < negativeClusterRadius s := by
  classical
  have hs : ‖a‖ ^ 2 / (2 * |a.re|) ≤
      ∑ b ∈ s.toFinset, ‖b‖ ^ 2 / (2 * |b.re|) := by
    apply Finset.single_le_sum (s := s.toFinset)
      (f := fun b : ℂ => ‖b‖ ^ 2 / (2 * |b.re|)) (a := a)
    · intro b _
      exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))
    · exact Multiset.mem_toFinset.mpr ha
  unfold negativeClusterRadius
  linarith

lemma dist_sq_negative_real_center (a : ℂ) (T : ℝ) :
    dist a (-(T : ℂ)) ^ 2 = ‖a‖ ^ 2 + T ^ 2 + 2 * T * a.re := by
  rw [dist_eq_norm, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, sub_zero]
  ring

/-- The explicit circle separates a finite root multiset with nonzero real
parts into its left and right clusters, without choosing root labels. -/
theorem negativeClusterRadius_separates (s : Multiset ℂ)
    (haxis : ∀ a ∈ s, a.re ≠ 0) {a : ℂ} (ha : a ∈ s) :
    a ∉ sphere (-(negativeClusterRadius s : ℂ)) (negativeClusterRadius s) ∧
      (a ∈ ball (-(negativeClusterRadius s : ℂ)) (negativeClusterRadius s) ↔
        a.re < 0) := by
  have hT := negativeClusterRadius_pos s
  have hdist := dist_sq_negative_real_center a (negativeClusterRadius s)
  by_cases hi : a.re < 0
  · have hratio := negativeClusterRadius_gt_ratio s ha
    rw [abs_of_neg hi] at hratio
    have hmul := (div_lt_iff₀
      (mul_pos (by norm_num : (0 : ℝ) < 2) (neg_pos.mpr hi))).1 hratio
    have hlt : dist a (-(negativeClusterRadius s : ℂ)) < negativeClusterRadius s := by
      apply (sq_lt_sq₀ dist_nonneg hT.le).1
      nlinarith [hmul, hdist]
    refine ⟨?_, ⟨fun _ => hi, fun _ => hlt⟩⟩
    intro hs
    have he := Metric.mem_sphere.mp hs
    linarith
  · have hre : 0 < a.re := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm (haxis a ha))
    have hprod : 0 < negativeClusterRadius s * a.re := mul_pos hT hre
    have hgt : negativeClusterRadius s < dist a (-(negativeClusterRadius s : ℂ)) := by
      apply (sq_lt_sq₀ hT.le dist_nonneg).1
      nlinarith [sq_nonneg ‖a‖, hdist, hprod]
    refine ⟨?_, ⟨?_, fun hp => False.elim (hi hp)⟩⟩
    · intro hs
      have he := Metric.mem_sphere.mp hs
      linarith
    · intro hb
      have hlt : dist a (-(negativeClusterRadius s : ℂ)) < negativeClusterRadius s := hb
      linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[simp] lemma exteriorPencil_zero (H Y : Matrix ι ι ℂ) : exteriorPencil H Y 0 = H⁻¹ := by
  simp [exteriorPencil]

lemma analyticAt_exteriorPencil (H Y : Matrix ι ι ℂ) (w : ℂ) :
    AnalyticAt ℂ (exteriorPencil H Y) w := by
  unfold exteriorPencil
  fun_prop

/-- The full root multiset of a Hermitian inverse is real and avoids zero. -/
lemma hermitian_inverse_root_re_ne_zero {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hdet : IsUnit H.det)
    {a : ℂ} (ha : a ∈ H⁻¹.charpoly.roots) : a.re ≠ 0 := by
  have him : a.im = 0 := by
    have hr := ha
    rw [hH.inv.roots_charpoly_eq_eigenvalues] at hr
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hr
    simp
  have hn : a ≠ 0 := by
    intro he
    have hs : a ∈ spectrum ℂ H⁻¹ :=
      Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha)
    have hu : IsUnit H⁻¹ := (Matrix.isUnit_iff_isUnit_det H⁻¹).mpr
      (H.isUnit_nonsing_inv_det hdet)
    exact (spectrum.zero_notMem ℂ hu) (he ▸ hs)
  intro hre
  exact hn (Complex.ext hre him)

/-- At zero the chosen circle encloses exactly the strictly negative roots
of `H⁻¹`, counted with their full algebraic multiplicities and normalized by r. -/
theorem exteriorClusterQ_zero {H : Matrix ι ι ℂ} (Y : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    exteriorClusterQ H Y 0 =
      (H⁻¹.charpoly.roots.map (fun a => if a.re < 0 then a else 0)).sum /
        (Fintype.card ι : ℂ) := by
  classical
  unfold exteriorClusterQ
  rw [exteriorPencil_zero, circleClusterTrace_eq_root_sum _
    (negativeClusterRadius_pos _).le
    (fun a ha => (negativeClusterRadius_separates _
      (fun b hb => hermitian_inverse_root_re_ne_zero hH hdet hb) ha).1)]
  apply congrArg (fun t : ℂ => t / (Fintype.card ι : ℂ))
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro a ha
  rw [(negativeClusterRadius_separates _
    (fun b hb => hermitian_inverse_root_re_ne_zero hH hdet hb) ha).2]

/-- The same contour, fixed at zero, lies in the resolvent set of `K(w)`
throughout a common complex neighborhood of zero. -/
theorem eventually_exterior_fixed_circle_resolvent {H : Matrix ι ι ℂ}
    (Y : Matrix ι ι ℂ) (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    let R := negativeClusterRadius H⁻¹.charpoly.roots
    ∀ᶠ w in 𝓝 (0 : ℂ), ∀ ζ ∈ sphere (-(R : ℂ)) R,
      ζ ∉ spectrum ℂ (exteriorPencil H Y w) := by
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  have hsub : spectrum ℂ (exteriorPencil H Y 0) ⊆ (sphere (-(R : ℂ)) R)ᶜ := by
    rw [exteriorPencil_zero]
    intro a ha hs
    have hr : a ∈ H⁻¹.charpoly.roots :=
      (Polynomial.mem_roots H⁻¹.charpoly_monic.ne_zero).2
        (Matrix.mem_spectrum_iff_isRoot_charpoly.mp ha)
    exact (negativeClusterRadius_separates _
      (fun b hb => hermitian_inverse_root_re_ne_zero hH hdet hb) hr).1 hs
  have hhemi : UpperHemicontinuousAt
      (fun w => spectrum ℂ (exteriorPencil H Y w)) 0 :=
    ((upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).upperHemicontinuousAt
      (exteriorPencil H Y 0)).comp (analyticAt_exteriorPencil H Y 0).continuousAt
  filter_upwards [hhemi.forall_isOpen _ isClosed_sphere.isOpen_compl hsub] with w hw
  intro ζ hζ hs
  exact hw hs hζ

/-- Joint integrand with parameter first and contour coordinate second. -/
def exteriorTraceJoint (H Y : Matrix ι ι ℂ) (p : ℂ × ℂ) : ℂ :=
  Matrix.trace (exteriorPencil H Y p.1 * resolvent (exteriorPencil H Y p.1) p.2)

set_option backward.isDefEq.respectTransparency false in
lemma analyticAt_exteriorTraceJoint (H Y : Matrix ι ι ℂ) {p : ℂ × ℂ}
    (hp : p.2 ∉ spectrum ℂ (exteriorPencil H Y p.1)) :
    AnalyticAt ℂ (exteriorTraceJoint H Y) p := by
  have hK : AnalyticAt ℂ (fun q : ℂ × ℂ => exteriorPencil H Y q.1) p :=
    (analyticAt_exteriorPencil H Y p.1).comp analyticAt_fst
  have hscalar : AnalyticAt ℂ
      (fun q : ℂ × ℂ => algebraMap ℂ (Matrix ι ι ℂ) q.2) p := by
    convert! (analyticAt_snd (𝕜 := ℂ) (p := p)).smul
      (analyticAt_const (v := (1 : Matrix ι ι ℂ))) using 1 <;>
      simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply] <;>
      (funext q; rfl)
  have hu : IsUnit (algebraMap ℂ (Matrix ι ι ℂ) p.2 - exteriorPencil H Y p.1) :=
    spectrum.notMem_iff.mp hp
  have hinv : AnalyticAt ℂ Ring.inverse
      (algebraMap ℂ (Matrix ι ι ℂ) p.2 - exteriorPencil H Y p.1) := by
    simpa only [hu.unit_spec] using analyticAt_inverse (𝕜 := ℂ) hu.unit
  have hres : AnalyticAt ℂ
      (fun q : ℂ × ℂ => resolvent (exteriorPencil H Y q.1) q.2) p :=
    hinv.comp (f := fun q : ℂ × ℂ =>
      algebraMap ℂ (Matrix ι ι ℂ) q.2 - exteriorPencil H Y q.1) (hscalar.sub hK)
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  exact (tr.analyticAt _).comp (hK.mul hres)

/-- Analyticity of the literal source exterior cluster function near zero.
Only Hermiticity and invertibility of H are needed for this step. -/
theorem analyticAt_exteriorClusterQ_zero {H : Matrix ι ι ℂ} (Y : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    AnalyticAt ℂ (exteriorClusterQ H Y) 0 := by
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  have hR : 0 ≤ R := (negativeClusterRadius_pos _).le
  have hF : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ ζ ∈ sphere (-(R : ℂ)) |R|,
      AnalyticAt ℂ (exteriorTraceJoint H Y) (w, ζ) := by
    filter_upwards [eventually_exterior_fixed_circle_resolvent Y hH hdet] with w hw
    intro ζ hζ
    exact analyticAt_exteriorTraceJoint H Y (hw ζ (by simpa only [abs_of_nonneg hR] using hζ))
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [hF.eventually_nhds] with w hw
  have hd := (hasDerivAt_circleIntegral_of_joint_analytic hw).differentiableAt
  exact (hd.div_const (2 * Real.pi * Complex.I : ℂ)).div_const (Fintype.card ι : ℂ)

end
end CGLMPBounds.Hardy
