module

public import CGLMPBounds.Hardy.CauchyMomentDisk
public import CGLMPBounds.Hardy.CircleCauchySecond

@[expose] public section


/-! Genuine extension of polynomial moments to holomorphic functions on
a strictly enclosing disk. All circle and measure interchanges follow
from continuity on a compact product. The moment premise is explicit and
is discharged by C.10 in the matrix application. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Polynomial Filter Set MeasureTheory Metric Complex
open scoped Topology

lemma norm_bound_ne_circle {a ζ : ℂ} {M R : ℝ}
    (ha : ‖a‖ ≤ M) (hMR : M < R) (hζ : ζ ∈ sphere 0 R) : ζ - a ≠ 0 := by
  intro he
  have hz : ‖ζ‖ = R := by simpa only [mem_sphere, dist_zero_right] using hζ
  have : ζ = a := sub_eq_zero.mp he
  rw [this] at hz
  linarith

lemma weighted_cauchy_moment_on_circle
    (P Q : Multiset ℂ) (r σ : ℂ) {K : Set ℂ} (hK : IsCompact K)
    (μ : Measure ℂ) [IsFiniteMeasure μ] {M R : ℝ} (hM : 0 < M) (hMR : M < R)
    (hP : ∀ a ∈ P, ‖a‖ ≤ M) (hQ : ∀ a ∈ Q, ‖a‖ ≤ M)
    (hKM : ∀ a ∈ K, ‖a‖ ≤ M)
    (hmoment : ∀ n : ℕ,
      (P.map (fun a => a ^ n)).sum / r - (Q.map (fun a => a ^ n)).sum / r =
        σ * (∫ ζ in K, (X ^ n : ℂ[X]).derivative.derivative.eval ζ ∂μ))
    {ζ : ℂ} (hζ : ζ ∈ sphere 0 R) :
    (P.map (fun a => 1 / (ζ - a))).sum / r -
      (Q.map (fun a => 1 / (ζ - a))).sum / r =
        σ * (∫ a in K, 2 / (ζ - a) ^ 3 ∂μ) := by
  have hR : 0 < R := hM.trans hMR
  have hnζ : ‖ζ‖ = R := by simpa only [mem_sphere, dist_zero_right] using hζ
  have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.mp (by rw [hnζ]; exact hR.ne')
  have hw : ‖ζ⁻¹‖ < 1 / M := by
    rw [norm_inv, hnζ, ← one_div]
    exact one_div_lt_one_div_of_lt hM hMR
  have he := weighted_cauchy_moment_resolvent_disk P Q r σ hK μ hM hP hQ hKM hmoment hw
  have hlinear (S : Multiset ℂ) (hS : ∀ a ∈ S, ‖a‖ ≤ M) :
      ζ⁻¹ * (S.map (fun a => 1 / (1 - ζ⁻¹ * a))).sum =
        (S.map (fun a => 1 / (ζ - a))).sum := by
    rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro a ha
    have h₁ := one_sub_mul_ne_zero_of_norm_bound hM hw (hS a ha)
    have h₂ := norm_bound_ne_circle (hS a ha) hMR hζ
    field_simp
  have hk : ζ⁻¹ * (∫ a in K, 2 * (ζ⁻¹) ^ 2 / (1 - ζ⁻¹ * a) ^ 3 ∂μ) =
      ∫ a in K, 2 / (ζ - a) ^ 3 ∂μ := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hK.measurableSet
    intro a ha
    have h₁ := one_sub_mul_ne_zero_of_norm_bound hM hw (hKM a ha)
    have h₂ := norm_bound_ne_circle (hKM a ha) hMR hζ
    field_simp <;> ring
  have hh := congrArg (fun z : ℂ => ζ⁻¹ * z) he
  simpa only [mul_sub, ← mul_div_assoc, hlinear P hP, hlinear Q hQ,
    mul_left_comm ζ⁻¹ σ, hk] using hh

theorem holomorphic_identity_of_polynomial_moments
    (P Q : Multiset ℂ) (r σ : ℂ) {K : Set ℂ} (hK : IsCompact K)
    (μ : Measure ℂ) [IsFiniteMeasure μ] {M R : ℝ} (hM : 0 < M) (hMR : M < R)
    (hP : ∀ a ∈ P, ‖a‖ ≤ M) (hQ : ∀ a ∈ Q, ‖a‖ ≤ M)
    (hKM : ∀ a ∈ K, ‖a‖ ≤ M)
    (hmoment : ∀ n : ℕ,
      (P.map (fun a => a ^ n)).sum / r - (Q.map (fun a => a ^ n)).sum / r =
        σ * (∫ ζ in K, (X ^ n : ℂ[X]).derivative.derivative.eval ζ ∂μ))
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    (P.map f).sum / r - (Q.map f).sum / r =
      σ * (∫ ζ in K, iteratedDeriv 2 f ζ ∂μ) := by
  have hR : 0 ≤ R := (hM.trans hMR).le
  have hsep (S : Multiset ℂ) (hS : ∀ a ∈ S, ‖a‖ ≤ M) :
      ∀ a ∈ S, a ∉ sphere 0 R := by
    intro a ha hs
    exact norm_bound_ne_circle (hS a ha) hMR hs (sub_self a)
  have hin (S : Multiset ℂ) (hS : ∀ a ∈ S, ‖a‖ ≤ M) :
      ∀ a ∈ S, a ∈ ball 0 R := by
    intro a ha
    simpa only [mem_ball, dist_zero_right] using (hS a ha).trans_lt hMR
  let J (S : Multiset ℂ) : ℂ → ℂ :=
    fun ζ => (S.map (fun a => f ζ / (ζ - a))).sum / r
  have hJi (S : Multiset ℂ) (hS : ∀ a ∈ S, ‖a‖ ≤ M) : CircleIntegrable (J S) 0 R := by
    simpa only [J, div_eq_mul_inv, mul_comm, Pi.smul_def, smul_eq_mul] using!
      (holomorphicRootFractionSum_circleIntegrable S hR hf (hsep S hS)).const_smul
        (a := r⁻¹)
  have hJ (S : Multiset ℂ) (hS : ∀ a ∈ S, ‖a‖ ≤ M) :
      (∮ ζ in C(0, R), J S ζ) = (2 * Real.pi * Complex.I : ℂ) * (S.map f).sum / r := by
    have hr : (∮ ζ in C(0, R), J S ζ) =
        (∮ ζ in C(0, R), (S.map (fun a => f ζ / (ζ - a))).sum) / r := by
      simpa only [J, div_eq_mul_inv, smul_eq_mul] using
        circleIntegral.integral_smul_const
          (fun ζ => (S.map (fun a => f ζ / (ζ - a))).sum) r⁻¹ 0 R
    rw [hr, circleIntegral_holomorphicRootFractionSum S hR hf (hsep S hS)]
    congr 2
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro a ha
    simp only [if_pos (hin S hS a ha)]
  have hpoint : ∀ ζ ∈ sphere 0 R,
      J P ζ - J Q ζ = σ * ∫ a in K, 2 * f ζ / (ζ - a) ^ 3 ∂μ := by
    intro ζ hζ
    have he := congrArg (fun z : ℂ => f ζ * z)
      (weighted_cauchy_moment_on_circle P Q r σ hK μ hM hMR hP hQ hKM hmoment hζ)
    have hsum (S : Multiset ℂ) :
        f ζ * (S.map (fun a => 1 / (ζ - a))).sum =
          (S.map (fun a => f ζ / (ζ - a))).sum := by
      rw [← Multiset.sum_map_mul_left]
      simp only [mul_one_div]
    rw [mul_sub, ← mul_div_assoc, hsum P, ← mul_div_assoc, hsum Q] at he
    calc
      J P ζ - J Q ζ = f ζ * (σ * ∫ a in K, 2 / (ζ - a) ^ 3 ∂μ) := he
      _ = σ * ∫ a in K, f ζ * (2 / (ζ - a) ^ 3) ∂μ := by
        rw [mul_left_comm (f ζ) σ, ← integral_const_mul]
      _ = _ := by
        congr 1
        apply setIntegral_congr_fun hK.measurableSet
        intro a ha
        ring
  have hF : ContinuousOn (fun p : ℂ × ℂ => 2 * f p.1 / (p.1 - p.2) ^ 3)
      (sphere 0 R ×ˢ K) := by
    apply ContinuousOn.div
    · exact continuousOn_const.mul
        ((hf.continuousOn.mono sphere_subset_closedBall).comp continuousOn_fst
          (fun p hp => hp.1))
    · fun_prop
    · intro p hp
      exact pow_ne_zero _ (norm_bound_ne_circle (hKM p.2 hp.2) hMR hp.1)
  have hc : (∮ ζ in C(0, R), J P ζ - J Q ζ) =
      σ * ∫ a in K, (2 * Real.pi * Complex.I : ℂ) * iteratedDeriv 2 f a ∂μ := by
    rw [circleIntegral.integral_congr hR hpoint, circleIntegral.integral_const_mul,
      circleIntegral_integral_compact_swap hK μ hR hF]
    congr 1
    apply setIntegral_congr_fun hK.measurableSet
    intro a ha
    exact circleIntegral_second_cauchy hR hf
      (by simpa only [mem_ball, dist_zero_right] using (hKM a ha).trans_lt hMR)
  rw [circleIntegral.integral_sub (hJi P hP) (hJi Q hQ), hJ P hP, hJ Q hQ,
    integral_const_mul] at hc
  have hconst : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  apply mul_left_cancel₀ hconst
  convert hc using 1 <;> ring

end
end CGLMPBounds.Hardy
