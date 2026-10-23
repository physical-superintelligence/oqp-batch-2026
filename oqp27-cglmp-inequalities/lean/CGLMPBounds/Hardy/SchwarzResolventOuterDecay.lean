module

public import CGLMPBounds.Hardy.SchwarzRationalTrace
public import Mathlib.Analysis.Normed.Operator.Asymptotics
public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section


/-! Actual decay at infinity of the C.7 weighted noncommutative trace and
vanishing of its large-circle integral. The inverse-square rate is derived
from Mathlib's resolvent estimate and the actual finite-dimensional trace,
not supplied as a matrix theorem hypothesis. -/

open Complex Metric Filter Set Asymptotics Bornology
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem weighted_resolvent_trace_isBigO_inverse_square
    (H Y : Matrix ι ι ℂ) {n : ℕ} (hn : 2 ≤ n) :
    (fun z : ℂ => z ^ (n - 2) * Matrix.trace ((resolvent H z * Y) ^ n))
      =O[cobounded ℂ] (fun z : ℂ => (z⁻¹) ^ 2) := by
  let mulY : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ :=
    ContinuousLinearMap.mulLeftRight ℂ (Matrix ι ι ℂ) 1 Y
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have hY : (fun z : ℂ => resolvent H z * Y) =O[cobounded ℂ] (fun z : ℂ => z⁻¹) := by
    have hm := (mulY.isBigO_comp (resolvent H) (cobounded ℂ)).trans (spectrum.resolvent_isBigO_inv H)
    simpa only [mulY, ContinuousLinearMap.mulLeftRight_apply, Matrix.one_mul] using hm
  have ht : (fun z : ℂ => Matrix.trace ((resolvent H z * Y) ^ n))
      =O[cobounded ℂ] (fun z : ℂ => (z⁻¹) ^ n) :=
    (tr.isBigO_comp (fun z : ℂ => (resolvent H z * Y) ^ n) (cobounded ℂ)).trans (hY.pow n)
  have hw := (isBigO_refl (fun z : ℂ => z ^ (n - 2)) (cobounded ℂ)).mul ht
  apply hw.congr' Filter.EventuallyEq.rfl
  filter_upwards [isBounded_singleton (x := (0 : ℂ))] with z hz
  have hpow : (z⁻¹) ^ n = (z⁻¹) ^ (n - 2) * (z⁻¹) ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  rw [hpow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hz, one_pow, one_mul]

/-- A genuine inverse-square bound forces the actual circle integral to
vanish as the radius tends to infinity. No integrability oracle is needed
for the norm estimate; subsequent rational comparison supplies integrability. -/
lemma tendsto_circleIntegral_zero_of_isBigO_inverse_square {f : ℂ → ℂ}
    (hf : f =O[cobounded ℂ] (fun z : ℂ => (z⁻¹) ^ 2)) :
    Tendsto (fun R : ℝ => ∮ z in C(0, R), f z) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := hf.exists_pos
  obtain ⟨R₀, _, hR₀⟩ := atTop_basis_Ioi.cobounded_of_norm.eventually_iff.mp hbound.bound
  have hb : ∀ᶠ R : ℝ in atTop,
      ‖∮ z in C(0, R), f z‖ ≤ (2 * Real.pi * C) / R := by
    filter_upwards [eventually_gt_atTop (max R₀ 0)] with R hR
    have hRp : 0 < R := (le_max_right _ _).trans_lt hR
    have hcircle : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C / R ^ 2 := by
      intro z hz
      have he : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
      have hzbound := hR₀ (x := z) (by
        change R₀ < ‖z‖
        rw [he]
        exact (le_max_left _ _).trans_lt hR)
      simpa only [norm_pow, norm_inv, he, inv_pow, div_eq_mul_inv] using hzbound
    calc
      ‖∮ z in C(0, R), f z‖ ≤ 2 * Real.pi * R * (C / R ^ 2) :=
        circleIntegral.norm_integral_le_of_norm_le_const hRp.le hcircle
      _ = (2 * Real.pi * C) / R := by field_simp [hRp.ne'] <;> ring
  apply squeeze_zero_norm' hb
  exact tendsto_const_nhds.div_atTop tendsto_id

theorem tendsto_weighted_resolvent_outerCircle_zero
    (H Y : Matrix ι ι ℂ) {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun R : ℝ => ∮ z in C(0, R),
      z ^ (n - 2) * Matrix.trace ((resolvent H z * Y) ^ n)) atTop (𝓝 0) :=
  tendsto_circleIntegral_zero_of_isBigO_inverse_square
    (weighted_resolvent_trace_isBigO_inverse_square H Y hn)

end
end CGLMPBounds.Hardy
