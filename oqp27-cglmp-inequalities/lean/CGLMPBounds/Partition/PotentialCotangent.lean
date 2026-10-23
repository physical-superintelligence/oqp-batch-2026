module

public import CGLMPBounds.Defs.ScalarPartition
public import CGLMPBounds.Partition.SincRegularity

@[expose] public section


/-! The explicit cotangent-moment differentiation behind (vf)'' = b−S.
This module is a local calculus ingredient. -/

namespace CGLMPBounds.Partition
open Filter
open scoped Topology
noncomputable section

private def cotangentMoment (a u : ℝ) : ℝ :=
  u * Real.cos (a * u) / Real.sin (a * u)

private def cotangentMomentFirst (a u : ℝ) : ℝ :=
  Real.cos (a * u) / Real.sin (a * u) - a * u / Real.sin (a * u) ^ 2

private lemma sin_scale_hasDerivAt (a u : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (a * t)) (a * Real.cos (a * u)) u := by
  convert ((hasDerivAt_id u).const_mul a).sin using 1
  · rfl
  · simp only [id_eq, mul_one]
    ring

private lemma cos_scale_hasDerivAt (a u : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (a * t)) (-a * Real.sin (a * u)) u := by
  convert ((hasDerivAt_id u).const_mul a).cos using 1
  · rfl
  · simp only [id_eq, mul_one]
    ring

private lemma cot_scale_hasDerivAt (a u : ℝ) (hs : Real.sin (a * u) ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.cos (a * t) / Real.sin (a * t))
      (-a / Real.sin (a * u) ^ 2) u := by
  have h := (cos_scale_hasDerivAt a u).div (sin_scale_hasDerivAt a u) hs
  convert h using 1
  field_simp [hs]
  have hsum := congrArg (fun t : ℝ => a * t) (Real.sin_sq_add_cos_sq (a * u))
  nlinarith [hsum]

private lemma cotangentMoment_hasDerivAt (a u : ℝ) (hs : Real.sin (a * u) ≠ 0) :
    HasDerivAt (cotangentMoment a) (cotangentMomentFirst a u) u := by
  have h := (hasDerivAt_id u).mul (cot_scale_hasDerivAt a u hs)
  convert h using 1
  · funext t
    simp only [cotangentMoment, Pi.mul_apply, id_eq]
    ring
  · simp only [cotangentMomentFirst, id_eq]
    ring

private lemma cotangentMomentFirst_hasDerivAt (a u : ℝ) (hs : Real.sin (a * u) ≠ 0) :
    HasDerivAt (cotangentMomentFirst a)
      (-2 * a * ((1 - (a * u) * Real.cot (a * u)) / Real.sin (a * u) ^ 2)) u := by
  have h := (cot_scale_hasDerivAt a u hs).sub
    (((hasDerivAt_id u).const_mul a).div ((sin_scale_hasDerivAt a u).pow 2)
      (pow_ne_zero 2 hs))
  convert h using 1
  · rfl
  · rw [Real.cot_eq_cos_div_sin]
    simp only [Pi.pow_apply, id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one]
    field_simp [hs]
    <;> ring

lemma iteratedDeriv_two_cotangentMoment (a u : ℝ) (hs : Real.sin (a * u) ≠ 0) :
    iteratedDeriv 2 (fun t : ℝ => t * Real.cos (a * t) / Real.sin (a * t)) u =
      -2 * a * scalarCotangentRemainder (a * u) := by
  have harg : a * u ≠ 0 := by
    intro h
    apply hs
    rw [h, Real.sin_zero]
  have he : deriv (cotangentMoment a) =ᶠ[𝓝 u] cotangentMomentFirst a := by
    filter_upwards [(sin_scale_hasDerivAt a u).continuousAt.eventually_ne hs] with t ht
    exact (cotangentMoment_hasDerivAt a t ht).deriv
  change iteratedDeriv 2 (cotangentMoment a) u = _
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
    he.deriv_eq, (cotangentMomentFirst_hasDerivAt a u hs).deriv,
    scalarCotangentRemainder, if_neg harg]

def regularizedCotangentMoment (u : ℝ) : ℝ :=
  (2 / Real.pi) * Real.cos ((Real.pi / 2) * u) / Real.sinc ((Real.pi / 2) * u)

lemma analyticAt_regularizedCotangentMoment {u : ℝ} (hu : |u| ≤ 1) :
    AnalyticAt ℝ regularizedCotangentMoment u := by
  have hs : 0 < Real.sinc ((Real.pi / 2) * u) := by
    apply Real.sinc_pos
    rw [abs_mul, abs_of_pos (show 0 < Real.pi / 2 by positivity)]
    have h := mul_le_mul_of_nonneg_left hu (show 0 ≤ Real.pi / 2 by positivity)
    nlinarith [Real.pi_pos]
  unfold regularizedCotangentMoment
  have hn : AnalyticAt ℝ
      (fun t : ℝ => (2 / Real.pi) * Real.cos ((Real.pi / 2) * t)) u := by
    fun_prop
  have hi : AnalyticAt ℝ (fun t : ℝ => (Real.pi / 2) * t) u := by fun_prop
  exact hn.div ((analyticAt_real_sinc _).comp hi) hs.ne'

lemma regularizedCotangentMoment_eq {u : ℝ} (hu : u ≠ 0) :
    regularizedCotangentMoment u =
      u * Real.cos ((Real.pi / 2) * u) / Real.sin ((Real.pi / 2) * u) := by
  have harg : (Real.pi / 2) * u ≠ 0 := mul_ne_zero (by positivity) hu
  unfold regularizedCotangentMoment
  rw [Real.sinc_of_ne_zero harg, div_div_eq_mul_div]
  congr 1
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- The source cotangent term has precisely the required negative second
 derivative away from its removable center. -/
theorem regularizedCotangentMoment_second_nonzero {u : ℝ}
    (hu : u ≠ 0) (hs : Real.sin ((Real.pi / 2) * u) ≠ 0) :
    iteratedDeriv 2 (fun t : ℝ => regularizedCotangentMoment t / Real.pi) u =
      -scalarCotangentRemainder ((Real.pi / 2) * u) := by
  have he : regularizedCotangentMoment =ᶠ[𝓝 u]
      (fun t : ℝ => t * Real.cos ((Real.pi / 2) * t) / Real.sin ((Real.pi / 2) * t)) := by
    filter_upwards [eventually_ne_nhds hu] with t ht
    exact regularizedCotangentMoment_eq ht
  simp_rw [div_eq_mul_inv]
  rw [iteratedDeriv_mul_const_field, he.iteratedDeriv_eq 2,
    iteratedDeriv_two_cotangentMoment (Real.pi / 2) u hs]
  field_simp [Real.pi_ne_zero]
  <;> ring

end
end CGLMPBounds.Partition
