module

public import CGLMPBounds.Hardy.SchwarzEllipseLimit
public import CGLMPBounds.Hardy.SchwarzSlitOuter
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section


/-!
# The actual Schwarz--slit representation (C.8)

The annulus identity and both actual contour limits give the formula at every
exterior Joukowski image. A quadratic-root argument supplies such a preimage
for every nonreal point. The source density's exact support then replaces the
finite enclosing interval by the real line. All functions and coefficients are
the literal normalized source objects; no analytic/moment oracle is assumed.

Source: complete supplement, printed p.8, equation (C.8).
-/

open Complex Matrix Filter Set Metric MeasureTheory
open scoped Topology Interval Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

/-- A genuine algebraic exterior preimage, rather than a chosen inverse-map
oracle. Complex algebraic closedness supplies the square root of z²-a². -/
lemma exists_slitJoukowski_preimage {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im ≠ 0) :
    ∃ s : ℂ, 1 < ‖s‖ ∧ slitJoukowski a s = z := by
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  obtain ⟨q, hq⟩ := IsAlgClosed.exists_pow_nat_eq (z ^ 2 - (a : ℂ) ^ 2) (by norm_num : 0 < 2)
  let u : ℂ := (z + q) / a
  let v : ℂ := (z - q) / a
  have huv : u * v = 1 := by
    dsimp [u, v]
    rw [div_mul_div_comm]
    apply (div_eq_iff (mul_ne_zero hac hac)).mpr
    linear_combination -hq
  have hsum : u + v = 2 * z / a := by
    dsimp [u, v]
    ring
  have hJ : ∀ s t : ℂ, s * t = 1 → s + t = 2 * z / a → slitJoukowski a s = z := by
    intro s t hst hstsum
    have hsn : s ≠ 0 := by
      intro he
      simpa [he] using hst
    have hi : s⁻¹ = t := by
      apply mul_left_cancel₀ hsn
      rw [mul_inv_cancel₀ hsn, hst]
    rw [slitJoukowski, hi, hstsum]
    push_cast
    field_simp [hac]
    <;> ring
  have hJu : slitJoukowski a u = z := hJ u v huv hsum
  have hJv : slitJoukowski a v = z := hJ v u (by rwa [mul_comm]) (by rwa [add_comm])
  have hstrict : ∀ s : ℂ, 1 ≤ ‖s‖ → slitJoukowski a s = z → 1 < ‖s‖ := by
    intro s hs he
    rcases lt_or_eq_of_le hs with hs | hs
    · exact hs
    · have hi := congrArg Complex.im he
      rw [slitJoukowski_im, Complex.normSq_eq_norm_sq, ← hs] at hi
      simp only [one_pow, div_one, sub_self, mul_zero, zero_mul] at hi
      exact (hz hi.symm).elim
  by_cases hu : 1 ≤ ‖u‖
  · exact ⟨u, hstrict u hu hJu, hJu⟩
  · have hnu : ‖u‖ < 1 := lt_of_not_ge hu
    have hn : ‖u‖ * ‖v‖ = 1 := by simpa only [norm_mul, norm_one] using congrArg norm huv
    have hv : 1 < ‖v‖ := by
      by_contra! hv
      have hm := mul_le_mul_of_nonneg_left hv (norm_nonneg u)
      nlinarith
    exact ⟨v, hv, hJv⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem regularizedReflectedTrace_slitJoukowski_eq_integral
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {a : ℝ} (ha : 0 < a)
    (hYbound : |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)| ≤ a)
    {s : ℂ} (hs : 1 < ‖s‖) (hz : (slitJoukowski a s).im ≠ 0) :
    regularizedReflectedTrace H Y (slitJoukowski a s) =
      ∫ x in (-a)..a, (traceDensity H Y x : ℂ) / ((x : ℂ) - slitJoukowski a s) := by
  have ht := tendsto_slitPullbackKernel_inner hH hY hdet ha hYbound hs hz
  have hevent : (fun r : ℝ => ∮ w in C(0, r), slitPullbackKernel H Y a s w) =ᶠ[𝓝[>] 1]
      (fun _ => -(2 * Real.pi * Complex.I : ℂ) *
        regularizedReflectedTrace H Y (slitJoukowski a s)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hs).filter_mono nhdsWithin_le_nhds] with r hr hrs
    exact slitPullbackKernel_inner_eq hH hY hdet ha hYbound hr hrs
  have hc := tendsto_const_nhds.congr' hevent.symm
  have heq := tendsto_nhds_unique hc ht
  apply mul_left_cancel₀ (a := -(2 * Real.pi * Complex.I : ℂ)) _ heq
  exact neg_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)

theorem regularizedReflectedTrace_eq_intervalIntegral
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {a : ℝ} (ha : 0 < a)
    (hYbound : |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)| ≤ a)
    {z : ℂ} (hz : z.im ≠ 0) :
    regularizedReflectedTrace H Y z =
      ∫ x in (-a)..a, (traceDensity H Y x : ℂ) / ((x : ℂ) - z) := by
  obtain ⟨s, hs, rfl⟩ := exists_slitJoukowski_preimage ha hz
  exact regularizedReflectedTrace_slitJoukowski_eq_integral hH hY hdet ha hYbound hs hz

/-- The actual full-line Cauchy transform of the supported density. -/
theorem regularizedReflectedTrace_eq_integral
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {z : ℂ} (hz : z.im ≠ 0) :
    regularizedReflectedTrace H Y z =
      ∫ x : ℝ, (traceDensity H Y x : ℂ) / ((x : ℂ) - z) := by
  let M : ℝ := |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)|
  let a : ℝ := M + 1
  have hM : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have ha : 0 < a := by dsimp [a]; linarith
  have hbound : |sInf (spectrum ℝ Y)| + |sSup (spectrum ℝ Y)| ≤ a := by
    change M ≤ M + 1
    linarith
  rw [regularizedReflectedTrace_eq_intervalIntegral hH hY hdet ha hbound hz,
    intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
  apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hxout : x ∉ Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y)) := by
    intro hxs
    apply hx
    have hlo := neg_abs_le (sInf (spectrum ℝ Y))
    have hhi := le_abs_self (sSup (spectrum ℝ Y))
    have hal := abs_nonneg (sInf (spectrum ℝ Y))
    have hau := abs_nonneg (sSup (spectrum ℝ Y))
    dsimp [a, M]
    constructor <;> linarith [hxs.1, hxs.2]
  simp only [traceDensity_eq_zero_outside_spectralInterval hH hY hdet hxout,
    Complex.ofReal_zero, zero_div]

/-- Equation (C.8) for the actual normalized strictly-upper pencil trace,
with the actual Taylor coefficients q₀,q₁ and literal supported density. -/
theorem upperClusterTrace_eq_affine_add_cauchyIntegral
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {z : ℂ} (hz : 0 < z.im) :
    upperClusterTrace (traceDensityPencil H Y z) =
      -exteriorTaylorCoefficient H Y 0 * z - exteriorTaylorCoefficient H Y 1 +
        ∫ x : ℝ, (traceDensity H Y x : ℂ) / ((x : ℂ) - z) := by
  have he := regularizedReflectedTrace_eq_integral hH hY hdet hz.ne'
  rw [regularizedReflectedTrace, reflectedPencilTrace_eq_upper hH hY hdet hz] at he
  linear_combination he

end
end CGLMPBounds.Hardy
