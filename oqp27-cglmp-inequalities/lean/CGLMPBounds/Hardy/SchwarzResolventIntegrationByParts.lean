module

public import CGLMPBounds.Hardy.SchwarzResolventDerivative
public import Mathlib.MeasureTheory.Integral.CircleIntegral

@[expose] public section


/-!
# Actual contour integration by parts for (C.7)

The primitive lambda^(k-1)*Tr[(R_H(lambda)Y)^k] has zero derivative integral
around a closed circle avoiding the spectrum. Its explicit derivative gives
the factor (k-1)/k used in the source positive-cluster coefficient calculation.
Circle integrability is established from the actual resolvent continuity;
the equality does not rely on totalized nonintegrable contour values.

This is a generic off-spectrum circle identity, not an assumption of the
source's desired moment formula.
-/

open Complex Matrix Filter Metric Set
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma continuousOn_matrix_resolvent (H : Matrix ι ι ℂ) {s : Set ℂ}
    (hs : ∀ z ∈ s, z ∉ spectrum ℂ H) : ContinuousOn (resolvent H) s := by
  intro z hz
  exact (hasDerivAt_matrix_resolvent H (hs z hz)).continuousAt.continuousWithinAt

theorem circleIntegral_resolvent_power_integrationByParts
    (H Y : Matrix ι ι ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hsep : ∀ z ∈ sphere c R, z ∉ spectrum ℂ H) {k : ℕ} (hk : 2 ≤ k) :
    (k : ℂ) * (∮ z in C(c, R), z ^ (k - 1) *
        Matrix.trace ((resolvent H z * Y) ^ k * resolvent H z)) =
      ((k - 1 : ℕ) : ℂ) * (∮ z in C(c, R), z ^ (k - 2) *
        Matrix.trace ((resolvent H z * Y) ^ k)) := by
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have hcR := continuousOn_matrix_resolvent H hsep
  have hcT : ContinuousOn (fun z => Matrix.trace ((resolvent H z * Y) ^ k)) (sphere c R) :=
    tr.continuous.comp_continuousOn ((hcR.mul continuousOn_const).pow k)
  have hcU : ContinuousOn (fun z => Matrix.trace
      ((resolvent H z * Y) ^ k * resolvent H z)) (sphere c R) :=
    tr.continuous.comp_continuousOn (((hcR.mul continuousOn_const).pow k).mul hcR)
  have hintT : CircleIntegrable (fun z => z ^ (k - 2) *
      Matrix.trace ((resolvent H z * Y) ^ k)) c R :=
    ((continuousOn_id.pow (k - 2)).mul hcT).circleIntegrable hR
  have hintU : CircleIntegrable (fun z => z ^ (k - 1) *
      Matrix.trace ((resolvent H z * Y) ^ k * resolvent H z)) c R :=
    ((continuousOn_id.pow (k - 1)).mul hcU).circleIntegrable hR
  have hintA : CircleIntegrable (fun z => ((k - 1 : ℕ) : ℂ) *
      (z ^ (k - 2) * Matrix.trace ((resolvent H z * Y) ^ k))) c R := by
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      (hintT.const_smul (a := ((k - 1 : ℕ) : ℂ)))
  have hintB : CircleIntegrable (fun z => (k : ℂ) *
      (z ^ (k - 1) * Matrix.trace ((resolvent H z * Y) ^ k * resolvent H z))) c R := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! (hintU.const_smul (a := (k : ℂ)))
  have hzero : (∮ z in C(c, R),
      ((k - 1 : ℕ) : ℂ) * (z ^ (k - 2) * Matrix.trace ((resolvent H z * Y) ^ k)) -
        (k : ℂ) * (z ^ (k - 1) * Matrix.trace ((resolvent H z * Y) ^ k * resolvent H z))) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR
      (f := fun z => z ^ (k - 1) * Matrix.trace ((resolvent H z * Y) ^ k))
    intro z hz
    have ht := hasDerivAt_trace_resolvent_mul_pow H Y (hsep z hz) (by omega : 0 < k)
    have hd := (hasDerivAt_pow (k - 1) z).mul ht
    have hn : k - 1 - 1 = k - 2 := by omega
    have hder : HasDerivAt (fun z => z ^ (k - 1) * Matrix.trace ((resolvent H z * Y) ^ k))
        (((k - 1 : ℕ) : ℂ) * (z ^ (k - 2) * Matrix.trace ((resolvent H z * Y) ^ k)) -
          (k : ℂ) * (z ^ (k - 1) * Matrix.trace ((resolvent H z * Y) ^ k * resolvent H z))) z := by
      convert hd using 1
      rw [hn]
      ring
    exact hder.hasDerivWithinAt
  rw [circleIntegral.integral_sub hintA hintB, circleIntegral.integral_const_mul,
    circleIntegral.integral_const_mul] at hzero
  linear_combination -hzero

/-- Solving the actual contour identity exposes the source's exact ratio. -/
theorem circleIntegral_resolvent_power_eq_ratio
    (H Y : Matrix ι ι ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hsep : ∀ z ∈ sphere c R, z ∉ spectrum ℂ H) {k : ℕ} (hk : 2 ≤ k) :
    (∮ z in C(c, R), z ^ (k - 1) *
      Matrix.trace ((resolvent H z * Y) ^ k * resolvent H z)) =
      (((k - 1 : ℕ) : ℂ) / (k : ℂ)) * (∮ z in C(c, R), z ^ (k - 2) *
        Matrix.trace ((resolvent H z * Y) ^ k)) := by
  have he := circleIntegral_resolvent_power_integrationByParts H Y hR hsep hk
  have hkn : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  apply (mul_left_cancel₀ hkn)
  calc
    (k : ℂ) * _ = ((k - 1 : ℕ) : ℂ) * _ := he
    _ = (k : ℂ) * _ := by field_simp [hkn] <;> ring

end
end CGLMPBounds.Hardy
