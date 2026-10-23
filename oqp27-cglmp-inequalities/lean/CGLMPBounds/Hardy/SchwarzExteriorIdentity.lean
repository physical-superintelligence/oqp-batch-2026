module

public import CGLMPBounds.Hardy.SchwarzExteriorImaginary
public import Mathlib.Analysis.Analytic.IsolatedZeros

@[expose] public section


/-!
# The actual upper exterior identity g(z) = -z q(1/z)

Inversion sends the upper exterior to a convex lower half-disk. Both the
inverted upper-cluster function and the literal q contour are analytic there.
Their equality on its negative imaginary segment follows from the complete
characteristic-root scaling formula. Analytic uniqueness then gives equality
throughout the half-disk and hence on the entire upper exterior.

No continuously chosen eigenvalues, arbitrary contour, analytic continuation
oracle or target identity is assumed in the final theorem. This is the source
p. 8 exterior step preceding C.8.
-/

open Complex Metric Set Filter
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

/-- Uniqueness on a lower half-disk from equality on its imaginary segment.
The punctured-neighborhood hypothesis of analytic uniqueness is supplied by
the injective real parameterization, not by an assumed open equality set. -/
lemma analytic_eqOn_lowerHalfDisk_of_imaginary_segment {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R ∩ {z : ℂ | z.im < 0}))
    (hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) R ∩ {z : ℂ | z.im < 0}))
    (heq : ∀ t : ℝ, 0 < t → t < R → f (-(t : ℂ) * Complex.I) = g (-(t : ℂ) * Complex.I)) :
    EqOn f g (ball (0 : ℂ) R ∩ {z : ℂ | z.im < 0}) := by
  let line : ℝ → ℂ := fun t => -(t : ℂ) * Complex.I
  let t₀ : ℝ := R / 2
  have ht₀ : 0 < t₀ := by dsimp [t₀]; positivity
  have ht₀R : t₀ < R := by dsimp [t₀]; linarith
  have hline : Continuous line := by dsimp [line]; fun_prop
  have hinj : Function.Injective line := by
    intro a b hab
    have hi := congrArg Complex.im hab
    simpa [line] using hi
  have hnorm : ‖line t₀‖ = t₀ := by
    simp [line, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₀]
  have hmem : line t₀ ∈ ball (0 : ℂ) R ∩ {z : ℂ | z.im < 0} := by
    constructor
    · simpa only [mem_ball_iff_norm, sub_zero, hnorm] using ht₀R
    · simpa [line] using neg_neg_of_pos ht₀
  have hconv : Convex ℝ (ball (0 : ℂ) R ∩ {z : ℂ | z.im < 0}) :=
    (convex_ball (0 : ℂ) R).inter
      (convex_halfSpace_lt Complex.imCLM.toLinearMap.isLinear 0)
  have htend : Tendsto line (𝓝[≠] t₀) (𝓝[≠] line t₀) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hline.tendsto t₀).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    change line t ≠ line t₀
    change t ≠ t₀ at ht
    exact fun he => ht (hinj he)
  have hevent : ∀ᶠ t in 𝓝 t₀, f (line t) = g (line t) := by
    filter_upwards [Ioo_mem_nhds ht₀ ht₀R] with t ht
    exact heq t ht.1 ht.2
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hconv.isPreconnected hmem
    (htend.frequently (hevent.filter_mono nhdsWithin_le_nhds).frequently)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- Auxiliary function obtained from the actual normalized source g by
inversion. It is not a new definition of q or a boundary selector. -/
def invertedUpperCluster (H Y : Matrix ι ι ℂ) (w : ℂ) : ℂ :=
  (-w) * upperClusterTrace (traceDensityPencil H Y w⁻¹)

lemma analyticAt_invertedUpperCluster {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {w : ℂ} (hw : w.im < 0) : AnalyticAt ℂ (invertedUpperCluster H Y) w := by
  have hwn : w ≠ 0 := by intro he; simp [he] at hw
  have hinv : 0 < w⁻¹.im := by
    rw [Complex.inv_im]
    exact div_pos (neg_pos.mpr hw) (Complex.normSq_pos.mpr hwn)
  have hg := analyticOnNhd_pencil_upperClusterTrace hH hY hdet w⁻¹ hinv
  exact analyticAt_id.neg.mul (hg.comp (analyticAt_inv hwn))

/-- Root scaling gives equality with the strict left cluster on the whole
negative imaginary axis, prior to identifying that cluster with q near zero. -/
lemma invertedUpperCluster_negative_imaginary (H Y : Matrix ι ι ℂ)
    (t : ℝ) (ht : 0 < t) :
    invertedUpperCluster H Y (-(t : ℂ) * Complex.I) =
      negativeClusterTrace (exteriorPencil H Y (-(t : ℂ) * Complex.I)) := by
  let w : ℂ := -(t : ℂ) * Complex.I
  have hwn : w ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast ht.ne')) Complex.I_ne_zero
  have hform : -(w⁻¹) = -((t⁻¹ : ℝ) : ℂ) * Complex.I := by
    simp only [w, mul_inv_rev, inv_neg, Complex.inv_I, Complex.ofReal_inv]
    ring
  change (-w) * upperClusterTrace (traceDensityPencil H Y w⁻¹) = _
  rw [traceDensityPencil_eq_exterior_smul H Y (inv_ne_zero hwn), inv_inv, hform,
    upperClusterTrace_neg_imag_smul _ t⁻¹ (inv_pos.mpr ht), ← hform,
    ← mul_assoc, neg_mul_neg, mul_inv_cancel₀ hwn, one_mul]

/-- Equality of the actual q and inverted g on a genuine complex lower
half-disk. Every analytic and cluster-selection premise is proved from the
source Hermitian/invertibility assumptions. -/
theorem exists_exteriorClusterQ_eq_inverted_lowerHalfDisk {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, ‖w‖ < ε → w.im < 0 →
      exteriorClusterQ H Y w = invertedUpperCluster H Y w := by
  obtain ⟨r, hr, hA⟩ := (analyticAt_exteriorClusterQ_zero Y hH hdet).exists_ball_analyticOnNhd
  obtain ⟨δ, hδ, hq⟩ := Metric.eventually_nhds_iff_ball.mp
    (exteriorClusterQ_eventuallyEq_negativeClusterTrace Y hH hdet)
  let ε := min r δ
  have hε : 0 < ε := lt_min hr hδ
  have hQA : AnalyticOnNhd ℂ (exteriorClusterQ H Y)
      (ball (0 : ℂ) ε ∩ {w : ℂ | w.im < 0}) := by
    intro w hw
    exact hA w (Metric.ball_subset_ball (min_le_left r δ) hw.1)
  have hGA : AnalyticOnNhd ℂ (invertedUpperCluster H Y)
      (ball (0 : ℂ) ε ∩ {w : ℂ | w.im < 0}) :=
    fun w hw => analyticAt_invertedUpperCluster hH hY hdet hw.2
  have hid := analytic_eqOn_lowerHalfDisk_of_imaginary_segment hε hQA hGA (by
    intro t ht htε
    have hn : ‖-(t : ℂ) * Complex.I‖ = t := by
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hm : -(t : ℂ) * Complex.I ∈ ball (0 : ℂ) δ := by
      rw [mem_ball_iff_norm, sub_zero, hn]
      exact htε.trans_le (min_le_right r δ)
    exact (hq _ hm).trans (invertedUpperCluster_negative_imaginary H Y t ht).symm)
  refine ⟨ε, hε, ?_⟩
  intro w hw hwi
  exact hid ⟨by simpa only [mem_ball_iff_norm, sub_zero] using hw, hwi⟩

/-- The exact exterior relation asserted before (C.8), on every sufficiently
large upper-half-plane parameter, with the source 1/r normalization. -/
theorem exists_upperClusterTrace_eq_exterior {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R < ‖z‖ → 0 < z.im →
      upperClusterTrace (traceDensityPencil H Y z) = (-z) * exteriorClusterQ H Y z⁻¹ := by
  obtain ⟨ε, hε, heq⟩ := exists_exteriorClusterQ_eq_inverted_lowerHalfDisk hH hY hdet
  refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
  intro z hz hzi
  have hzn : z ≠ 0 := by intro he; simp [he] at hzi
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hzn
  have hmul := mul_lt_mul_of_pos_left hz hε
  rw [mul_inv_cancel₀ hε.ne'] at hmul
  have hdiv : 1 / ‖z‖ < ε := (div_lt_iff₀ hzpos).mpr (by nlinarith)
  have hnorm : ‖z⁻¹‖ < ε := by simpa only [norm_inv, one_div] using hdiv
  have him : z⁻¹.im < 0 := by
    rw [Complex.inv_im]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hzi) (Complex.normSq_pos.mpr hzn)
  have he := congrArg (fun a : ℂ => (-z) * a) (heq z⁻¹ hnorm him)
  dsimp only [invertedUpperCluster] at he
  rw [inv_inv, ← mul_assoc, neg_mul_neg, mul_inv_cancel₀ hzn, one_mul] at he
  exact he.symm

end
end CGLMPBounds.Hardy
