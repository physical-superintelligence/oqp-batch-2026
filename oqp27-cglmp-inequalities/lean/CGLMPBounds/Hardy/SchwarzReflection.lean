module

public import CGLMPBounds.Hardy.UpperClusterBoundaryFull
public import CGLMPBounds.Hardy.SchwarzRectangleSplit
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Topology.Piecewise

@[expose] public section


/-!
# Schwarz reflection of the actual source upper-cluster boundary extension

The upper bank is the genuine continuous boundary limit, not the strict
upper-root selector evaluated on real arguments. Conjugation defines the lower
bank. The banks agree off the exact real spectral interval of Y, and rectangle
Morera removes the real-axis seam there. The result retains normalization 1/r.

Canonical supplement, Lemma C.3, printed p.8, the Schwarz-reflection step before
C.8. This file does not assert the slit integral or any moment formula.
-/

open Complex Matrix Filter Set Metric
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- Continuous folding into the closed upper half-plane. -/
def closedUpperFold (z : ℂ) : {w : ℂ // 0 ≤ w.im} :=
  ⟨(z.re : ℂ) + ((|z.im| : ℝ) : ℂ) * Complex.I, by simp⟩

lemma continuous_closedUpperFold : Continuous closedUpperFold := by
  apply Continuous.subtype_mk
  exact (Complex.continuous_ofReal.comp Complex.continuous_re).add
    ((Complex.continuous_ofReal.comp Complex.continuous_im.abs).mul continuous_const)

lemma closedUpperFold_coe_of_nonneg {z : ℂ} (hz : 0 ≤ z.im) :
    (closedUpperFold z : ℂ) = z := by
  apply Complex.ext <;> simp [closedUpperFold, abs_of_nonneg hz]

lemma closedUpperFold_coe_of_nonpos {z : ℂ} (hz : z.im ≤ 0) :
    (closedUpperFold z : ℂ) = star z := by
  apply Complex.ext <;> simp [closedUpperFold, abs_of_nonpos hz, Complex.star_def]

/-- The exact source interval viewed as a closed subset of the complex plane. -/
def spectralSlit (Y : Matrix ι ι ℂ) : Set ℂ :=
  {z | z.im = 0 ∧ z.re ∈ Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y))}

lemma isClosed_spectralSlit (Y : Matrix ι ι ℂ) : IsClosed (spectralSlit Y) := by
  exact (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_Icc.preimage Complex.continuous_re)

lemma isOpen_spectralSlit_compl (Y : Matrix ι ι ℂ) : IsOpen (spectralSlit Y)ᶜ :=
  (isClosed_spectralSlit Y).isOpen_compl

/-- The actual upper extension and its conjugate lower reflection. Values on
the slit itself are assigned the upper bank; holomorphy is only claimed off it. -/
def reflectedPencilTrace (H Y : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then pencilUpperBoundaryExtension H Y (closedUpperFold z)
  else star (pencilUpperBoundaryExtension H Y (closedUpperFold z))

theorem reflectedPencilTrace_eq_upper
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {z : ℂ} (hz : 0 < z.im) :
    reflectedPencilTrace H Y z = upperClusterTrace (traceDensityPencil H Y z) := by
  have heq : closedUpperFold z = upperHalfPlaneInclusion ⟨z, hz⟩ := by
    apply Subtype.ext
    exact closedUpperFold_coe_of_nonneg hz.le
  rw [reflectedPencilTrace, if_pos hz.le, heq]
  exact pencilUpperBoundaryExtension_eq_interior hH hY hdet ⟨z, hz⟩

theorem reflectedPencilTrace_eq_lower
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {z : ℂ} (hz : z.im < 0) :
    reflectedPencilTrace H Y z =
      star (upperClusterTrace (traceDensityPencil H Y (star z))) := by
  have hzs : 0 < (star z).im := by simpa [Complex.star_def] using neg_pos.mpr hz
  have heq : closedUpperFold z = upperHalfPlaneInclusion ⟨star z, hzs⟩ := by
    apply Subtype.ext
    exact closedUpperFold_coe_of_nonpos hz.le
  rw [reflectedPencilTrace, if_neg (not_le.mpr hz), heq,
    pencilUpperBoundaryExtension_eq_interior hH hY hdet ⟨star z, hzs⟩]

theorem reflectedPencilTrace_real (H Y : Matrix ι ι ℂ) (x : ℝ) :
    reflectedPencilTrace H Y (x : ℂ) =
      pencilUpperBoundaryExtension H Y ⟨(x : ℂ), by simp⟩ := by
  have heq : closedUpperFold (x : ℂ) = ⟨(x : ℂ), by simp⟩ := by
    apply Subtype.ext
    exact closedUpperFold_coe_of_nonneg (by simp)
  simp only [reflectedPencilTrace, Complex.ofReal_im, le_refl, if_true, heq]

/-- The two continuous branches match on the real seam outside the spectral
interval because the actual boundary imaginary part is the supported density. -/
theorem continuousOn_reflectedPencilTrace
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) :
    ContinuousOn (reflectedPencilTrace H Y) (spectralSlit Y)ᶜ := by
  have hC : Continuous (fun z =>
      pencilUpperBoundaryExtension H Y (closedUpperFold z)) :=
    (continuous_pencilUpperBoundaryExtension hH hY hdet).comp continuous_closedUpperFold
  apply ContinuousOn.if (f := fun z => pencilUpperBoundaryExtension H Y (closedUpperFold z))
    (g := fun z => star (pencilUpperBoundaryExtension H Y (closedUpperFold z)))
  · intro z hz
    have hz0 : z.im = 0 :=
      (frontier_le_subset_eq continuous_const Complex.continuous_im hz.2).symm
    have hx : z.re ∉ Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y)) := by
      intro hx
      exact hz.1 ⟨hz0, hx⟩
    have heq : closedUpperFold z = ⟨(z.re : ℂ), by simp⟩ := by
      apply Subtype.ext
      apply Complex.ext <;> simp [closedUpperFold, hz0]
    rw [heq]
    exact pencilUpperBoundaryExtension_eq_conj_outside_spectralInterval hH hY hdet hx
  · exact hC.continuousOn
  · exact hC.star.continuousOn

theorem differentiableAt_reflectedPencilTrace_off_real
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {z : ℂ} (hz : z.im ≠ 0) :
    DifferentiableAt ℂ (reflectedPencilTrace H Y) z := by
  rcases lt_or_gt_of_ne hz with hz | hz
  · have hzs : 0 < (star z).im := by simpa [Complex.star_def] using neg_pos.mpr hz
    have hd : DifferentiableAt ℂ
        (fun w => star (upperClusterTrace (traceDensityPencil H Y (star w)))) z := by
      simpa [Function.comp_def, Complex.star_def] using
        (differentiableAt_pencil_upperClusterTrace hH hY hdet hzs).star_conj
    apply hd.congr_of_eventuallyEq
    filter_upwards [Complex.continuous_im.continuousAt.eventually_lt continuousAt_const hz]
      with w hw
    exact reflectedPencilTrace_eq_lower hH hY hdet hw
  · apply (differentiableAt_pencil_upperClusterTrace hH hY hdet hz).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt Complex.continuous_im.continuousAt hz]
      with w hw
    exact reflectedPencilTrace_eq_upper hH hY hdet hw

/-- Schwarz reflection is established for the literal normalized source g on
the complement of the exact spectral interval, with no analytic extension
oracle among the hypotheses. -/
theorem analyticOnNhd_reflectedPencilTrace
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) :
    AnalyticOnNhd ℂ (reflectedPencilTrace H Y) (spectralSlit Y)ᶜ := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_spectralSlit_compl Y)
  apply differentiableOn_of_continuousOn_off_real (isOpen_spectralSlit_compl Y)
    (continuousOn_reflectedPencilTrace hH hY hdet)
  intro z _ hz
  exact differentiableAt_reflectedPencilTrace_off_real hH hY hdet hz

end
end CGLMPBounds.Hardy
