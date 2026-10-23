module

public import CGLMPBounds.Hardy.SchwarzSlitAnnulus
public import CGLMPBounds.Hardy.SchwarzCosineBanks
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section


/-!
# Literal ellipse parametrization of the pullback contour

These are exact coordinate and derivative identities, including the collapsed
ellipse r=1. They connect Mathlib's actual circle integral to an ordinary real
parameter integral. No contour-limit equality is assumed.
-/

open Complex Matrix Filter Set Metric MeasureTheory
open scoped Topology Interval Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

def slitEllipse (a r θ : ℝ) : ℂ :=
  (((a / 2) * (r + r⁻¹) * Real.cos θ : ℝ) : ℂ) +
    (((a / 2) * (r - r⁻¹) * Real.sin θ : ℝ) : ℂ) * Complex.I

def slitEllipseTangent (a r θ : ℝ) : ℂ :=
  ((-((a / 2) * (r + r⁻¹)) * Real.sin θ : ℝ) : ℂ) +
    (((a / 2) * (r - r⁻¹) * Real.cos θ : ℝ) : ℂ) * Complex.I

lemma slitJoukowski_circleMap (a r θ : ℝ) :
    slitJoukowski a (circleMap 0 r θ) = slitEllipse a r θ := by
  rw [slitJoukowski, circleMap_zero_inv]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.add_re, circleMap_zero_re, Real.cos_neg, slitEllipse,
      Complex.I_re, Complex.I_im, mul_zero]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.add_im, circleMap_zero_im, Real.sin_neg, slitEllipse,
      Complex.I_re, Complex.I_im, mul_one, mul_zero]
    ring

@[simp] lemma slitEllipse_re (a r θ : ℝ) :
    (slitEllipse a r θ).re = (a / 2) * (r + r⁻¹) * Real.cos θ := by
  simp only [slitEllipse, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

@[simp] lemma slitEllipse_im (a r θ : ℝ) :
    (slitEllipse a r θ).im = (a / 2) * (r - r⁻¹) * Real.sin θ := by
  simp only [slitEllipse, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]

@[simp] lemma slitEllipse_one (a θ : ℝ) :
    slitEllipse a 1 θ = ((a * Real.cos θ : ℝ) : ℂ) := by
  simp only [slitEllipse, inv_one, sub_self, mul_zero, zero_mul,
    Complex.ofReal_zero, add_zero]
  congr 1
  ring

@[simp] lemma slitEllipseTangent_one (a θ : ℝ) :
    slitEllipseTangent a 1 θ = ((-a * Real.sin θ : ℝ) : ℂ) := by
  simp only [slitEllipseTangent, inv_one, sub_self, mul_zero, zero_mul,
    Complex.ofReal_zero, add_zero]
  congr 1
  ring

lemma hasDerivAt_slitEllipse (a r θ : ℝ) :
    HasDerivAt (slitEllipse a r) (slitEllipseTangent a r θ) θ := by
  have hc := ((Real.hasDerivAt_cos θ).const_mul ((a / 2) * (r + r⁻¹))).ofReal_comp
  have hs := ((Real.hasDerivAt_sin θ).const_mul ((a / 2) * (r - r⁻¹))).ofReal_comp
  change HasDerivAt (fun y : ℝ =>
    (((a / 2) * (r + r⁻¹) * Real.cos y : ℝ) : ℂ) +
      (((a / 2) * (r - r⁻¹) * Real.sin y : ℝ) : ℂ) * Complex.I)
    (slitEllipseTangent a r θ) θ
  simpa only [slitEllipseTangent, mul_neg, neg_mul] using!
    hc.fun_add (hs.mul_const Complex.I)

lemma continuousAt_slitEllipse (a : ℝ) {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    ContinuousAt (fun q : ℝ × ℝ => slitEllipse a q.1 q.2) p := by
  unfold slitEllipse
  have hi : ContinuousAt (fun q : ℝ × ℝ => q.1⁻¹) p := continuousAt_fst.inv₀ hp
  have hc : ContinuousAt (fun q : ℝ × ℝ =>
      (a / 2) * (q.1 + q.1⁻¹) * Real.cos q.2) p :=
    (continuousAt_const.mul (continuousAt_fst.add hi)).mul
      (Real.continuous_cos.continuousAt.comp continuousAt_snd)
  have hs : ContinuousAt (fun q : ℝ × ℝ =>
      (a / 2) * (q.1 - q.1⁻¹) * Real.sin q.2) p :=
    (continuousAt_const.mul (continuousAt_fst.sub hi)).mul
      (Real.continuous_sin.continuousAt.comp continuousAt_snd)
  exact (Complex.continuous_ofReal.continuousAt.comp hc).add
    ((Complex.continuous_ofReal.continuousAt.comp hs).mul continuousAt_const)

lemma continuousAt_slitEllipseTangent (a : ℝ) {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    ContinuousAt (fun q : ℝ × ℝ => slitEllipseTangent a q.1 q.2) p := by
  unfold slitEllipseTangent
  have hi : ContinuousAt (fun q : ℝ × ℝ => q.1⁻¹) p := continuousAt_fst.inv₀ hp
  have hs : ContinuousAt (fun q : ℝ × ℝ =>
      -((a / 2) * (q.1 + q.1⁻¹)) * Real.sin q.2) p :=
    (continuousAt_const.mul (continuousAt_fst.add hi)).neg.mul
      (Real.continuous_sin.continuousAt.comp continuousAt_snd)
  have hc : ContinuousAt (fun q : ℝ × ℝ =>
      (a / 2) * (q.1 - q.1⁻¹) * Real.cos q.2) p :=
    (continuousAt_const.mul (continuousAt_fst.sub hi)).mul
      (Real.continuous_cos.continuousAt.comp continuousAt_snd)
  exact (Complex.continuous_ofReal.continuousAt.comp hs).add
    ((Complex.continuous_ofReal.continuousAt.comp hc).mul continuousAt_const)

lemma slitEllipseTangent_eq_chain (a : ℝ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    slitEllipseTangent a r θ = deriv (circleMap 0 r) θ *
      deriv (slitJoukowski a) (circleMap 0 r θ) := by
  have hwn : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr
  have hj := hasDerivAt_slitJoukowski a hwn
  have hc := hj.comp θ (hasDerivAt_circleMap 0 r θ)
  have he : (slitJoukowski a ∘ circleMap 0 r) = slitEllipse a r := by
    funext t
    exact slitJoukowski_circleMap a r t
  rw [he] at hc
  have hd := hc.unique (hasDerivAt_slitEllipse a r θ)
  rw [hj.deriv, deriv_circleMap]
  simpa only [mul_comm] using hd.symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- The actual circle pullback is literally the ellipse parameter integral.
This is an exact equality for every nonzero radius, before any limit. -/
theorem circleIntegral_slitPullbackKernel_eq_ellipse
    (H Y : Matrix ι ι ℂ) (a : ℝ) (s : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∮ w in C(0, r), slitPullbackKernel H Y a s w) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), slitEllipseTangent a r θ *
        (regularizedReflectedTrace H Y (slitEllipse a r θ) /
          (slitEllipse a r θ - slitJoukowski a s)) := by
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro θ _
  change deriv (circleMap 0 r) θ • slitPullbackKernel H Y a s (circleMap 0 r θ) =
    slitEllipseTangent a r θ *
      (regularizedReflectedTrace H Y (slitEllipse a r θ) /
        (slitEllipse a r θ - slitJoukowski a s))
  rw [slitPullbackKernel, slitJoukowski_circleMap, slitEllipseTangent_eq_chain a hr]
  simp only [smul_eq_mul]
  ring

end
end CGLMPBounds.Hardy
