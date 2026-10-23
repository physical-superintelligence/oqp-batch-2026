module

public import CGLMPBounds.Hardy.HardyPotentialNonrealBoundary
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section


/-! Actual horizontal concavity and the endpoint/center comparisons for C.14.
The nonreal hypothesis permits the true radial primitive to be continuous
at both endpoints before the separate real-corner argument. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Complex

lemma hasDerivAt_realPart_horizontal {f : ℂ → ℂ} {f' : ℂ} (x y : ℝ)
    (hf : HasDerivAt f f' ((x : ℂ) + Complex.I * y)) :
    HasDerivAt (fun u : ℝ => (f ((u : ℂ) + Complex.I * y)).re) f'.re x := by
  have hc : HasDerivAt (fun w : ℂ => f (w + Complex.I * y)) f' (x : ℂ) := by
    simpa only [mul_one, Function.comp_def, id_eq] using
      hf.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const _)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hc.comp_ofReal

lemma continuous_hardyStripRealPotential_horizontal {y : ℝ} (hy : y ≠ 0) :
    Continuous (fun x : ℝ => hardyStripRealPotential x y) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have ha := analyticAt_hardyStripPotential_nonreal
    (z := (x : ℂ) + Complex.I * y) (by simpa using hy)
  exact Complex.continuous_re.continuousAt.comp
    (ha.continuousAt.comp (f := fun u : ℝ => (u : ℂ) + Complex.I * y)
      (x := x) (by fun_prop))

theorem hardyStripRealPotential_concave_nonreal {y : ℝ} (hy : y ≠ 0) :
    ConcaveOn ℝ (Icc (-1 : ℝ) 1) (fun x => hardyStripRealPotential x y) := by
  let f' : ℝ → ℝ := fun x => (-segmentPrimitive hardyStripSecant
    ((x : ℂ) + Complex.I * y)).re
  let f'' : ℝ → ℝ := fun x => (-hardyStripSecant ((x : ℂ) + Complex.I * y)).re
  have hz {x : ℝ} (hx : x ∈ interior (Icc (-1 : ℝ) 1)) :
      (x : ℂ) + Complex.I * y ∈ openVerticalUnitStrip := by
    simpa [interior_Icc, openVerticalUnitStrip, abs_lt] using hx
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := f') (f'' := f'') (convex_Icc _ _)
    (continuous_hardyStripRealPotential_horizontal hy).continuousOn
  · intro x hx
    exact (hasDerivAt_realPart_horizontal x y (hasDerivAt_hardyStripPotential (hz hx))).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_realPart_horizontal x y
      (hasDerivAt_hardyStripFirstPrimitive (hz hx)).neg).hasDerivWithinAt
  · intro x hx
    exact neg_nonpos.mpr (hardyStripSecant_re_pos (hz hx)).le

theorem hardyStripRealPotential_endpoint_center_bounds {x y : ℝ}
    (hx : |x| ≤ 1) (hy : y ≠ 0) :
    |y| ≤ hardyStripRealPotential x y ∧
      hardyStripRealPotential x y ≤ hardyStripRealPotential 0 y := by
  have hc := hardyStripRealPotential_concave_nonreal hy
  have hxm : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
  have hnx : -x ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hxm.1, hxm.2]
  constructor
  · have h := hc.2 (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num)
      (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num)
      (show (0 : ℝ) ≤ (1-x)/2 by linarith [hxm.2])
      (show (0 : ℝ) ≤ (1+x)/2 by linarith [hxm.1]) (by ring)
    have he : (1-x)/2 * (-1 : ℝ) + (1+x)/2 * 1 = x := by ring
    simpa only [smul_eq_mul, he,
      (hardyStripRealPotential_boundary_nonzero y hy).1,
      (hardyStripRealPotential_boundary_nonzero y hy).2,
      ← add_mul, show (1-x)/2+(1+x)/2=1 by ring, one_mul] using h
  · have h := hc.2 hxm hnx
      (show (0 : ℝ) ≤ (1/2 : ℝ) by norm_num)
      (show (0 : ℝ) ≤ (1/2 : ℝ) by norm_num) (by norm_num)
    have he : (1/2 : ℝ)*x+(1/2 : ℝ)*(-x)=0 := by ring
    simpa only [smul_eq_mul, he, hardyStripRealPotential_even_x,
      ← add_mul, show (1/2 : ℝ)+1/2=1 by norm_num, one_mul] using h

end
end CGLMPBounds.Hardy
