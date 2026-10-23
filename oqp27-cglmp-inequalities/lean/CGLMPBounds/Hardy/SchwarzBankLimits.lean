module

public import CGLMPBounds.Hardy.SchwarzAffineRemainder
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section


/-!
# Actual limits of the two horizontal banks of the slit

Compact uniform continuity gives convergence of horizontal kernel integrals to
their genuine boundary values. Applied to the actual regularized upper-cluster
function, the upper-minus-lower bank limit is exactly 2πi times the density's
Cauchy integral on every finite interval. This is the inner-bank limit needed
for C.8; the outer-contour identity and its limiting argument remain separate.
-/

open Complex Matrix Filter Set Metric MeasureTheory
open scoped Topology Interval Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

/-- A compact-box continuity lemma for actual interval integrals. -/
lemma continuousAt_intervalIntegral_of_continuousOn_box
    (F : ℝ → ℝ → ℂ) (a b : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hF : ContinuousOn (Function.uncurry F) (Icc (-ε) ε ×ˢ [[a, b]])) :
    ContinuousAt (fun t => ∫ x in a..b, F t x) 0 := by
  have hU : Icc (-ε) ε ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (neg_neg_of_pos hε) hε
  have huc := (isCompact_Icc.prod isCompact_uIcc).uniformContinuousOn_of_continuous hF
  have hu : TendstoUniformlyOn F (F 0) (𝓝 (0 : ℝ)) [[a, b]] := by
    simpa only [nhdsWithin_eq_nhds.mpr hU] using
      huc.tendstoUniformlyOn (show (0 : ℝ) ∈ Icc (-ε) ε from ⟨by linarith, hε.le⟩)
  have hFc : ∀ᶠ t in 𝓝 (0 : ℝ), ContinuousOn (F t) [[a, b]] := by
    filter_upwards [hU] with t ht
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨ht, hx⟩)
  exact hu.tendsto_intervalIntegral_of_continuousOn hFc

/-- Moving a horizontal line to the real axis is continuous for a continuous
numerator and a genuinely nonreal pole. No contour-limit premise is assumed. -/
lemma continuousAt_horizontalKernelIntegral
    (G : ℂ → ℂ) (hG : Continuous G) (a b : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    ContinuousAt (fun t : ℝ => ∫ x in a..b,
      G ((x : ℂ) + (t : ℂ) * Complex.I) /
        ((x : ℂ) + (t : ℂ) * Complex.I - z)) 0 := by
  let ε : ℝ := |z.im| / 2
  have hε : 0 < ε := div_pos (abs_pos.mpr hz) (by norm_num)
  have hm : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
  apply continuousAt_intervalIntegral_of_continuousOn_box _ a b hε
  apply (hG.comp hm).continuousOn.div (hm.sub continuous_const).continuousOn
  intro p hp he
  have heIm : p.1 = z.im := by
    have hh := congrArg Complex.im he
    change (((p.2 : ℂ) + (p.1 : ℂ) * Complex.I) - z).im = 0 at hh
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
      zero_add, Complex.zero_im] at hh
    exact sub_eq_zero.mp hh
  have habs : |p.1| ≤ ε := abs_le.mpr hp.1
  rw [heIm] at habs
  dsimp only [ε] at habs
  have := abs_pos.mpr hz
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- Globally continuous folded upper bank, used solely to justify the actual
one-sided horizontal limits. -/
def regularizedFoldedUpperTrace (H Y : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  pencilUpperBoundaryExtension H Y (closedUpperFold z) +
    exteriorTaylorCoefficient H Y 0 * (closedUpperFold z : ℂ) +
    exteriorTaylorCoefficient H Y 1

lemma continuous_regularizedFoldedUpperTrace
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) : Continuous (regularizedFoldedUpperTrace H Y) := by
  exact (((continuous_pencilUpperBoundaryExtension hH hY hdet).comp continuous_closedUpperFold).add
    (continuous_const.mul (continuous_subtype_val.comp continuous_closedUpperFold))).add
      continuous_const

lemma regularizedFoldedUpperTrace_eq_of_nonneg
    (H Y : Matrix ι ι ℂ) {z : ℂ} (hz : 0 ≤ z.im) :
    regularizedFoldedUpperTrace H Y z = regularizedReflectedTrace H Y z := by
  simp only [regularizedFoldedUpperTrace, regularizedReflectedTrace, reflectedPencilTrace,
    if_pos hz, closedUpperFold_coe_of_nonneg hz]

lemma regularizedFoldedUpperTrace_star_eq_of_neg
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {z : ℂ} (hz : z.im < 0) :
    star (regularizedFoldedUpperTrace H Y z) = regularizedReflectedTrace H Y z := by
  simp only [regularizedFoldedUpperTrace, regularizedReflectedTrace, reflectedPencilTrace,
    if_neg (not_le.mpr hz), star_add, star_mul', exteriorTaylorCoefficient_star hH hY hdet,
    closedUpperFold_coe_of_nonpos hz.le, star_star]

/-- Exact upper-minus-lower horizontal bank limit with the source density and
the correct `2πi` sign. The nonreal pole keeps the fixed finite real interval
away from the kernel singularity. -/
theorem tendsto_regularized_horizontal_bank_difference
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (a b : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    Tendsto (fun ε : ℝ =>
      (∫ x in a..b, regularizedReflectedTrace H Y ((x : ℂ) + (ε : ℂ) * Complex.I) /
        ((x : ℂ) + (ε : ℂ) * Complex.I - z)) -
      (∫ x in a..b, regularizedReflectedTrace H Y ((x : ℂ) + (-(ε : ℂ)) * Complex.I) /
        ((x : ℂ) + (-(ε : ℂ)) * Complex.I - z)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((2 * Real.pi * Complex.I : ℂ) *
        ∫ x in a..b, (traceDensity H Y x : ℂ) / ((x : ℂ) - z))) := by
  let G := regularizedFoldedUpperTrace H Y
  have hG : Continuous G := continuous_regularizedFoldedUpperTrace hH hY hdet
  have hplus := continuousAt_horizontalKernelIntegral G hG a b z hz
  have hminus : ContinuousAt (fun ε : ℝ => ∫ x in a..b,
      star (G ((x : ℂ) + (-(ε : ℂ)) * Complex.I)) /
        ((x : ℂ) + (-(ε : ℂ)) * Complex.I - z)) 0 := by
    have hneg : ContinuousAt (fun ε : ℝ => -ε) 0 := by fun_prop
    have hc := (continuousAt_horizontalKernelIntegral (fun w => star (G w))
      hG.star a b z hz).comp_of_eq hneg (by simp)
    simpa only [Function.comp_def, Complex.ofReal_neg] using hc
  have hden : ∀ x : ℝ, (x : ℂ) - z ≠ 0 := by
    intro x hx
    have hh := congrArg Complex.im hx
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub] at hh
    exact hz (neg_eq_zero.mp hh)
  have hip : IntervalIntegrable (fun x : ℝ => G (x : ℂ) / ((x : ℂ) - z)) volume a b :=
    ((hG.comp Complex.continuous_ofReal).div
      (Complex.continuous_ofReal.sub continuous_const) hden).intervalIntegrable a b
  have him : IntervalIntegrable (fun x : ℝ => star (G (x : ℂ)) / ((x : ℂ) - z)) volume a b :=
    ((hG.comp Complex.continuous_ofReal).star.div
      (Complex.continuous_ofReal.sub continuous_const) hden).intervalIntegrable a b
  have hjump : (∫ x in a..b, G (x : ℂ) / ((x : ℂ) - z)) -
      (∫ x in a..b, star (G (x : ℂ)) / ((x : ℂ) - z)) =
      (2 * Real.pi * Complex.I : ℂ) *
        ∫ x in a..b, (traceDensity H Y x : ℂ) / ((x : ℂ) - z) := by
    rw [← intervalIntegral.integral_sub hip him, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [G]
    rw [← sub_div, regularizedFoldedUpperTrace_eq_of_nonneg H Y (by simp),
      regularizedReflectedTrace_sub_conj_real hH hY hdet]
    ring
  have hlim := (hplus.tendsto.sub hminus.tendsto).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simp only [Complex.ofReal_zero, neg_zero, zero_mul, add_zero] at hlim
  rw [hjump] at hlim
  apply Tendsto.congr' _ hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  congr 1 <;> apply intervalIntegral.integral_congr <;> intro x _
  all_goals dsimp only [G]
  · rw [regularizedFoldedUpperTrace_eq_of_nonneg H Y (by simpa using hε.le)]
  · rw [regularizedFoldedUpperTrace_star_eq_of_neg hH hY hdet (by simpa using neg_neg_of_pos hε)]

end
end CGLMPBounds.Hardy
