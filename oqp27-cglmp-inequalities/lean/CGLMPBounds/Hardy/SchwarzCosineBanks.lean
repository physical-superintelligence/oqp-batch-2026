module

public import CGLMPBounds.Hardy.SchwarzBankLimits
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section


/-!
# Exact cosine parametrization of the two limiting slit banks

The upper half of the limiting ellipse traverses a to -a; the lower half
traverses -a to a. Genuine real change of variables gives their sum as the
negative boundary jump integral, hence -2πi times the actual density integral.
This identifies the candidate limit without assuming convergence to it.
-/

open Complex Matrix Filter Set Metric MeasureTheory
open scoped Topology Interval Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

lemma continuous_realCauchyKernel (G : ℂ → ℂ) (hG : Continuous G)
    {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (fun x : ℝ => G (x : ℂ) / ((x : ℂ) - z)) := by
  apply (hG.comp Complex.continuous_ofReal).div
    (Complex.continuous_ofReal.sub continuous_const)
  intro x hx
  have hh := congrArg Complex.im hx
  simp only [Pi.sub_apply, Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub] at hh
  exact hz (neg_eq_zero.mp hh)

/-- Actual real substitution x=a cos θ, for arbitrary oriented endpoints. -/
lemma integral_cosineCauchyKernel (G : ℂ → ℂ) (hG : Continuous G)
    (a u v : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ θ in u..v, (-a * Real.sin θ) •
      (G ((a * Real.cos θ : ℝ) : ℂ) / (((a * Real.cos θ : ℝ) : ℂ) - z))) =
      ∫ x in (a * Real.cos u)..(a * Real.cos v), G (x : ℂ) / ((x : ℂ) - z) := by
  apply intervalIntegral.integral_deriv_smul_comp
    (f := fun θ => a * Real.cos θ) (f' := fun θ => -a * Real.sin θ)
    (g := fun x : ℝ => G (x : ℂ) / ((x : ℂ) - z))
  · intro θ _
    simpa only [mul_neg, neg_mul] using (Real.hasDerivAt_cos θ).const_mul a
  · exact (continuous_const.mul Real.continuous_sin).continuousOn
  · exact continuous_realCauchyKernel G hG hz

lemma integral_two_cosineBanks (G : ℂ → ℂ) (hG : Continuous G)
    (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ θ in (0 : ℝ)..Real.pi, (-a * Real.sin θ) •
      (G ((a * Real.cos θ : ℝ) : ℂ) / (((a * Real.cos θ : ℝ) : ℂ) - z))) +
    (∫ θ in Real.pi..(2 * Real.pi), (-a * Real.sin θ) •
      (star (G ((a * Real.cos θ : ℝ) : ℂ)) /
        (((a * Real.cos θ : ℝ) : ℂ) - z))) =
      -((∫ x in (-a)..a, G (x : ℂ) / ((x : ℂ) - z)) -
        (∫ x in (-a)..a, star (G (x : ℂ)) / ((x : ℂ) - z))) := by
  rw [integral_cosineCauchyKernel G hG a 0 Real.pi hz,
    integral_cosineCauchyKernel (fun w => star (G w)) hG.star
      a Real.pi (2 * Real.pi) hz]
  simp only [Real.cos_zero, Real.cos_pi, Real.cos_two_pi, mul_one, mul_neg_one]
  rw [intervalIntegral.integral_symm (-a) a]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- The actual limiting cosine-bank expression, with correct orientation and
the source's exact normalized trace density. No convergence premise is used. -/
theorem integral_regularized_cosineBanks
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ θ in (0 : ℝ)..Real.pi, (-a * Real.sin θ) •
      (regularizedFoldedUpperTrace H Y ((a * Real.cos θ : ℝ) : ℂ) /
        (((a * Real.cos θ : ℝ) : ℂ) - z))) +
    (∫ θ in Real.pi..(2 * Real.pi), (-a * Real.sin θ) •
      (star (regularizedFoldedUpperTrace H Y ((a * Real.cos θ : ℝ) : ℂ)) /
        (((a * Real.cos θ : ℝ) : ℂ) - z))) =
      -(2 * Real.pi * Complex.I : ℂ) *
        ∫ x in (-a)..a, (traceDensity H Y x : ℂ) / ((x : ℂ) - z) := by
  let G := regularizedFoldedUpperTrace H Y
  have hG : Continuous G := continuous_regularizedFoldedUpperTrace hH hY hdet
  rw [integral_two_cosineBanks G hG a hz]
  have hip := (continuous_realCauchyKernel G hG hz).intervalIntegrable (μ := volume) (-a) a
  have him := (continuous_realCauchyKernel (fun w => star (G w)) hG.star hz).intervalIntegrable
    (μ := volume) (-a) a
  have hjump : (∫ x in (-a)..a, G (x : ℂ) / ((x : ℂ) - z)) -
      (∫ x in (-a)..a, star (G (x : ℂ)) / ((x : ℂ) - z)) =
      (2 * Real.pi * Complex.I : ℂ) *
        ∫ x in (-a)..a, (traceDensity H Y x : ℂ) / ((x : ℂ) - z) := by
    rw [← intervalIntegral.integral_sub hip him, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    change G (x : ℂ) / ((x : ℂ) - z) - star (G (x : ℂ)) / ((x : ℂ) - z) = _
    dsimp only [G]
    rw [← sub_div, regularizedFoldedUpperTrace_eq_of_nonneg H Y (by simp),
      regularizedReflectedTrace_sub_conj_real hH hY hdet]
    ring
  rw [hjump]
  ring

end
end CGLMPBounds.Hardy
