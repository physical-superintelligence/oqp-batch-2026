module

public import CGLMPBounds.Defs.HardyExterior
public import CGLMPBounds.Hardy.SchwarzExteriorReality
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.TaylorSeries

@[expose] public section


/-!
# Real Taylor coefficients of the literal exterior cluster function

The coefficients are the actual complex derivatives of the contour function
q, divided by factorials. Their reality follows by restricting derivatives to
the real axis, where q is already proved real. The convergent Taylor expansion
uses Mathlib's analytic Taylor theorem. No moment or residue formula is used
to define the coefficients or assumed to identify them.

Source: supplement p. 8, the expansion `q(w)=Σ q_j w^j` preceding (C.8).
The relation to the actual upper-cluster g and the slit integral are still open.
-/

open Complex Filter Metric Set
open scoped Topology

namespace CGLMPBounds.Hardy
noncomputable section

/-- Local real-axis reality passes to the complex derivative, by uniqueness
of the real derivative of the imaginary part. -/
lemma eventually_deriv_im_eq_zero_of_real_germ {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (hreal : ∀ᶠ x : ℝ in 𝓝 0, (f (x : ℂ)).im = 0) :
    ∀ᶠ x : ℝ in 𝓝 0, (deriv f (x : ℂ)).im = 0 := by
  have hc : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hd := hc.eventually (analyticAt_iff_eventually_differentiableAt.mp hf)
  filter_upwards [hd, hreal.eventually_nhds] with x hx hxr
  have hi : HasDerivAt (fun y : ℝ => (f (y : ℂ)).im) (deriv f (x : ℂ)).im x := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt.comp_ofReal
  have hz : HasDerivAt (fun y : ℝ => (f (y : ℂ)).im) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hxr
  exact hi.unique hz

/-- All iterated complex derivatives are real on a real neighborhood of zero;
the neighborhood may depend on the derivative order. -/
lemma eventually_iteratedDeriv_im_eq_zero_of_real_germ {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (hreal : ∀ᶠ x : ℝ in 𝓝 0, (f (x : ℂ)).im = 0) (m : ℕ) :
    ∀ᶠ x : ℝ in 𝓝 0, (iteratedDeriv m f (x : ℂ)).im = 0 := by
  induction m generalizing f with
  | zero => simpa only [iteratedDeriv_zero] using hreal
  | succ m ih =>
    rw [iteratedDeriv_succ']
    exact ih hf.deriv (eventually_deriv_im_eq_zero_of_real_germ hf hreal)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem exteriorTaylorCoefficient_im_eq_zero {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) (m : ℕ) :
    (exteriorTaylorCoefficient H Y m).im = 0 := by
  have hi : (iteratedDeriv m (exteriorClusterQ H Y) 0).im = 0 := by
    simpa using (eventually_iteratedDeriv_im_eq_zero_of_real_germ
      (analyticAt_exteriorClusterQ_zero Y hH hdet)
      (eventually_exteriorClusterQ_im_eq_zero hH hY hdet) m).self_of_nhds
  simp [exteriorTaylorCoefficient, Complex.div_im, hi]

/-- There is a genuine convergent power-series expansion with precisely these
coefficients throughout a complex disk of positive radius. -/
theorem exists_exteriorTaylor_hasSum {H : Matrix ι ι ℂ} (Y : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, ‖w‖ < R →
      HasSum (fun m : ℕ => exteriorTaylorCoefficient H Y m * w ^ m)
        (exteriorClusterQ H Y w) := by
  obtain ⟨R, hR, hA⟩ := (analyticAt_exteriorClusterQ_zero Y hH hdet).exists_ball_analyticOnNhd
  refine ⟨R, hR, ?_⟩
  intro w hw
  have hmem : w ∈ ball (0 : ℂ) R := by simpa only [mem_ball_iff_norm, sub_zero] using hw
  convert Complex.hasSum_taylorSeries_on_ball hA.differentiableOn hmem using 1
  ext m
  simp only [exteriorTaylorCoefficient, smul_eq_mul, sub_zero, div_eq_mul_inv]
  ring

@[simp] theorem exteriorTaylorCoefficient_zero (H Y : Matrix ι ι ℂ) :
    exteriorTaylorCoefficient H Y 0 = exteriorClusterQ H Y 0 := by
  simp [exteriorTaylorCoefficient]

end
end CGLMPBounds.Hardy
