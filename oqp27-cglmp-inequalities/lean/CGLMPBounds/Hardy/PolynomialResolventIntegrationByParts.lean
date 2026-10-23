module

public import CGLMPBounds.Hardy.SchwarzResolventIntegrationByParts

@[expose] public section


/-! The C.10 coefficient variant of the genuine trace-resolvent contour
integration by parts. Polynomial degree and perturbation order are independent;
noncommutative multiplication is preserved until trace cyclicity is applied. -/

open Complex Matrix Filter Metric Set
open scoped Topology Matrix.Norms.Operator
namespace CGLMPBounds.Hardy
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem circleIntegral_polynomial_resolvent_integrationByParts
    (H Y : Matrix ι ι ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hsep : ∀ z ∈ sphere c R, z ∉ spectrum ℂ H) {k N : ℕ} (hk : 0 < k) (hN : 0 < N) :
    (k : ℂ) * (∮ z in C(c, R), z ^ N *
        Matrix.trace ((resolvent H z * Y) ^ k * resolvent H z)) =
      (N : ℂ) * (∮ z in C(c, R), z ^ (N - 1) *
        Matrix.trace ((resolvent H z * Y) ^ k)) := by
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have hcR := continuousOn_matrix_resolvent H hsep
  have hcT : ContinuousOn (fun z => Matrix.trace ((resolvent H z * Y) ^ k)) (sphere c R) :=
    tr.continuous.comp_continuousOn ((hcR.mul continuousOn_const).pow k)
  have hcU : ContinuousOn (fun z => Matrix.trace
      ((resolvent H z * Y) ^ k * resolvent H z)) (sphere c R) :=
    tr.continuous.comp_continuousOn (((hcR.mul continuousOn_const).pow k).mul hcR)
  have hintT : CircleIntegrable (fun z => z ^ (N - 1) *
      Matrix.trace ((resolvent H z * Y) ^ k)) c R :=
    ((continuousOn_id.pow (N - 1)).mul hcT).circleIntegrable hR
  have hintU : CircleIntegrable (fun z => z ^ N *
      Matrix.trace ((resolvent H z * Y) ^ k * resolvent H z)) c R :=
    ((continuousOn_id.pow N).mul hcU).circleIntegrable hR
  have hintA : CircleIntegrable (fun z => (N : ℂ) *
      (z ^ (N - 1) * Matrix.trace ((resolvent H z * Y) ^ k))) c R := by
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      (hintT.const_smul (a := (N : ℂ)))
  have hintB : CircleIntegrable (fun z => (k : ℂ) *
      (z ^ N * Matrix.trace ((resolvent H z * Y) ^ k * resolvent H z))) c R := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! (hintU.const_smul (a := (k : ℂ)))
  have hzero : (∮ z in C(c, R),
      (N : ℂ) * (z ^ (N - 1) * Matrix.trace ((resolvent H z * Y) ^ k)) -
        (k : ℂ) * (z ^ N * Matrix.trace ((resolvent H z * Y) ^ k * resolvent H z))) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR
      (f := fun z => z ^ N * Matrix.trace ((resolvent H z * Y) ^ k))
    intro z hz
    have ht := hasDerivAt_trace_resolvent_mul_pow H Y (hsep z hz) (by omega : 0 < k)
    have hd := (hasDerivAt_pow N z).mul ht
    have hder : HasDerivAt (fun z => z ^ N * Matrix.trace ((resolvent H z * Y) ^ k))
        ((N : ℂ) * (z ^ (N - 1) * Matrix.trace ((resolvent H z * Y) ^ k)) -
          (k : ℂ) * (z ^ N * Matrix.trace ((resolvent H z * Y) ^ k * resolvent H z))) z := by
      convert hd using 1
      ring
    exact hder.hasDerivWithinAt
  rw [circleIntegral.integral_sub hintA hintB, circleIntegral.integral_const_mul,
    circleIntegral.integral_const_mul] at hzero
  linear_combination -hzero

end
end CGLMPBounds.Hardy
