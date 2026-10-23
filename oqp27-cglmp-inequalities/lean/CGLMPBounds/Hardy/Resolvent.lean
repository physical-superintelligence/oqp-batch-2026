module

public import CGLMPBounds.Hardy.Pencil
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section


/-!
# Analytic pencil resolvents and their normalized trace integrand

These lemmas concern the actual pencil, not a chosen eigenvalue enumeration.
They supply the analytic integrand needed for the source's Riesz-cluster trace.
No Riesz projection, selected-root trace identity, boundary extension, or moment
identity is inferred merely from these local analyticity facts.
-/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix
open scoped Matrix.Norms.Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(ζI-L(z))⁻¹` on the resolvent set, using the standard algebra resolvent. -/
def pencilResolvent (H Y : Matrix ι ι ℂ) (ζ z : ℂ) : Matrix ι ι ℂ :=
  resolvent (traceDensityPencil H Y z) ζ

/-- The normalized trace integrand for `Tr(L(z) Π(z))/r`. The contour factor
`1/(2πi)` belongs to the later contour integral, not to this integrand. -/
def pencilTraceIntegrand (H Y : Matrix ι ι ℂ) (ζ z : ℂ) : ℂ :=
  Matrix.trace (traceDensityPencil H Y z * pencilResolvent H Y ζ z) /
    (Fintype.card ι : ℂ)

lemma analyticAt_traceDensityPencil (H Y : Matrix ι ι ℂ) (z : ℂ) :
    AnalyticAt ℂ (traceDensityPencil H Y) z := by
  unfold traceDensityPencil
  fun_prop

/-- Fixing a contour point outside the spectrum gives an analytic resolvent in z. -/
theorem analyticAt_pencilResolvent (H Y : Matrix ι ι ℂ) {ζ z : ℂ}
    (hζ : ζ ∉ spectrum ℂ (traceDensityPencil H Y z)) :
    AnalyticAt ℂ (pencilResolvent H Y ζ) z := by
  have hu : IsUnit (algebraMap ℂ (Matrix ι ι ℂ) ζ - traceDensityPencil H Y z) := by
    simpa only [spectrum.mem_iff, not_not] using hζ
  have hinv : AnalyticAt ℂ Ring.inverse
      (algebraMap ℂ (Matrix ι ι ℂ) ζ - traceDensityPencil H Y z) := by
    simpa only [hu.unit_spec] using analyticAt_inverse (𝕜 := ℂ) hu.unit
  have harg : AnalyticAt ℂ
      (fun w => algebraMap ℂ (Matrix ι ι ℂ) ζ - traceDensityPencil H Y w) z :=
    analyticAt_const.sub (analyticAt_traceDensityPencil H Y z)
  change AnalyticAt ℂ
    (fun w => Ring.inverse (algebraMap ℂ (Matrix ι ι ℂ) ζ - traceDensityPencil H Y w)) z
  exact hinv.comp (f := fun w =>
    algebraMap ℂ (Matrix ι ι ℂ) ζ - traceDensityPencil H Y w) harg

/-- The normalized trace of the resolvent integrand is analytic even when L(z)
has repeated or defective eigenvalues away from the fixed contour point. -/
theorem analyticAt_pencilTraceIntegrand (H Y : Matrix ι ι ℂ) {ζ z : ℂ}
    (hζ : ζ ∉ spectrum ℂ (traceDensityPencil H Y z)) :
    AnalyticAt ℂ (pencilTraceIntegrand H Y ζ) z := by
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have hprod : AnalyticAt ℂ
      (fun w => traceDensityPencil H Y w * pencilResolvent H Y ζ w) z :=
    (analyticAt_traceDensityPencil H Y z).mul (analyticAt_pencilResolvent H Y hζ)
  have ht : AnalyticAt ℂ
      (fun w => Matrix.trace (traceDensityPencil H Y w * pencilResolvent H Y ζ w)) z :=
    (tr.analyticAt _).comp hprod
  simpa only [pencilTraceIntegrand] using!
    (ht.div_const (c := (Fintype.card ι : ℂ)))

/-- Every real contour point is in the pencil resolvent set in the upper half-plane. -/
lemma real_not_mem_pencil_spectrum {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    (t : ℂ) ∉ spectrum ℂ (traceDensityPencil H Y z) := by
  intro ht
  exact pencil_spectrum_im_ne_zero hH hY hdet hz ht (by simp)

theorem analyticOnNhd_pencilTraceIntegrand_real {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) (t : ℝ) :
    AnalyticOnNhd ℂ (pencilTraceIntegrand H Y (t : ℂ)) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact analyticAt_pencilTraceIntegrand H Y (real_not_mem_pencil_spectrum hH hY hdet hz t)

end
end CGLMPBounds.Hardy
