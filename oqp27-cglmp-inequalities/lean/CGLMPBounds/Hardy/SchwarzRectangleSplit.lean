module

public import Mathlib.Analysis.Complex.HasPrimitives

@[expose] public section


/-!
# Removing a real-axis seam by rectangle splitting

A continuous complex function on an open set, holomorphic off the real axis,
is holomorphic on the whole open set. The proof splits crossing rectangles
along the real axis, applies Cauchy-Goursat on the two sides, cancels the common
edge, and applies Mathlib's rectangle form of Morera's theorem.

This is generic calculus for the forthcoming Schwarz reflection of the actual
upper-cluster boundary extension. It does not assume or assert a slit integral
representation.
-/

open Complex Metric Set Filter MeasureTheory
open scoped Topology Interval

namespace CGLMPBounds.Hardy
noncomputable section

/-- The positively oriented rectangular boundary expression used by Mathlib's
Cauchy theorem, with unrestricted orientations of the two real intervals. -/
def rectangleBoundaryIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x in a..b, f (x + c * Complex.I)) -
    (∫ x in a..b, f (x + d * Complex.I)) +
    Complex.I * (∫ y in c..d, f (b + y * Complex.I)) -
    Complex.I * (∫ y in c..d, f (a + y * Complex.I))

lemma rectangleBoundaryIntegral_swap_vertical (f : ℂ → ℂ) (a b c d : ℝ) :
    rectangleBoundaryIntegral f a b d c = -rectangleBoundaryIntegral f a b c d := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_symm d c, intervalIntegral.integral_symm d c]
  ring

/-- Additivity across a horizontal cut, with the needed integrability explicit. -/
lemma rectangleBoundaryIntegral_split (f : ℂ → ℂ) (a b c m d : ℝ)
    (ha₁ : IntervalIntegrable (fun y : ℝ => f (a + y * Complex.I)) volume c m)
    (ha₂ : IntervalIntegrable (fun y : ℝ => f (a + y * Complex.I)) volume m d)
    (hb₁ : IntervalIntegrable (fun y : ℝ => f (b + y * Complex.I)) volume c m)
    (hb₂ : IntervalIntegrable (fun y : ℝ => f (b + y * Complex.I)) volume m d) :
    rectangleBoundaryIntegral f a b c d =
      rectangleBoundaryIntegral f a b c m + rectangleBoundaryIntegral f a b m d := by
  have ha := intervalIntegral.integral_add_adjacent_intervals ha₁ ha₂
  have hb := intervalIntegral.integral_add_adjacent_intervals hb₁ hb₂
  simp only [rectangleBoundaryIntegral]
  rw [← ha, ← hb]
  ring

lemma rectangleBoundaryIntegral_eq_zero (f : ℂ → ℂ) (a b c d : ℝ)
    (hC : ContinuousOn f ([[a, b]] ×ℂ [[c, d]]))
    (hD : ∀ z ∈ Ioo (min a b) (max a b) ×ℂ Ioo (min c d) (max c d),
      DifferentiableAt ℂ f z) : rectangleBoundaryIntegral f a b c d = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f ((a : ℂ) + c * Complex.I) ((b : ℂ) + d * Complex.I) ∅ countable_empty
    (by simpa using hC) (by
      intro z hz
      apply hD z
      simpa using hz.1)
  simpa [rectangleBoundaryIntegral, smul_eq_mul] using h

lemma rectangleBoundaryIntegral_eq_zero_crossing (f : ℂ → ℂ) (a b c d : ℝ)
    (hc : c ≤ 0) (hd : 0 ≤ d)
    (hC : ContinuousOn f ([[a, b]] ×ℂ [[c, d]]))
    (hD : ∀ z ∈ Ioo (min a b) (max a b) ×ℂ Ioo c d,
      z.im ≠ 0 → DifferentiableAt ℂ f z) :
    rectangleBoundaryIntegral f a b c d = 0 := by
  have hmid : (0 : ℝ) ∈ [[c, d]] := by
    rw [uIcc_of_le (hc.trans hd)]
    exact ⟨hc, hd⟩
  have hlow : [[c, 0]] ⊆ [[c, d]] := uIcc_subset_uIcc_left hmid
  have hhigh : [[0, d]] ⊆ [[c, d]] := uIcc_subset_uIcc_right hmid
  have hClo : ContinuousOn f ([[a, b]] ×ℂ [[c, 0]]) :=
    hC.mono (fun _ hz => ⟨hz.1, hlow hz.2⟩)
  have hChi : ContinuousOn f ([[a, b]] ×ℂ [[0, d]]) :=
    hC.mono (fun _ hz => ⟨hz.1, hhigh hz.2⟩)
  have hlo : rectangleBoundaryIntegral f a b c 0 = 0 := by
    apply rectangleBoundaryIntegral_eq_zero f a b c 0 hClo
    intro z hz
    have hz' : z ∈ Ioo (min a b) (max a b) ×ℂ Ioo c 0 := by
      simpa only [min_eq_left hc, max_eq_right hc] using hz
    exact hD z ⟨hz'.1, hz'.2.1, hz'.2.2.trans_le hd⟩ (ne_of_lt hz'.2.2)
  have hhi : rectangleBoundaryIntegral f a b 0 d = 0 := by
    apply rectangleBoundaryIntegral_eq_zero f a b 0 d hChi
    intro z hz
    have hz' : z ∈ Ioo (min a b) (max a b) ×ℂ Ioo 0 d := by
      simpa only [min_eq_left hd, max_eq_right hd] using hz
    exact hD z ⟨hz'.1, hc.trans_lt hz'.2.1, hz'.2.2⟩ (ne_of_gt hz'.2.1)
  have hia : IntervalIntegrable (fun y : ℝ => f (a + y * Complex.I)) volume c d := by
    apply ContinuousOn.intervalIntegrable
    apply hC.comp (by fun_prop)
    intro y hy
    change ((a : ℂ) + y * Complex.I).re ∈ [[a, b]] ∧
      ((a : ℂ) + y * Complex.I).im ∈ [[c, d]]
    simpa using And.intro (left_mem_uIcc (a := a) (b := b)) hy
  have hib : IntervalIntegrable (fun y : ℝ => f (b + y * Complex.I)) volume c d := by
    apply ContinuousOn.intervalIntegrable
    apply hC.comp (by fun_prop)
    intro y hy
    change ((b : ℂ) + y * Complex.I).re ∈ [[a, b]] ∧
      ((b : ℂ) + y * Complex.I).im ∈ [[c, d]]
    simpa using And.intro (right_mem_uIcc (a := a) (b := b)) hy
  rw [rectangleBoundaryIntegral_split f a b c 0 d
    (hia.mono_set hlow) (hia.mono_set hhigh) (hib.mono_set hlow) (hib.mono_set hhigh),
    hlo, hhi, add_zero]

lemma rectangleBoundaryIntegral_eq_zero_off_real_ordered (f : ℂ → ℂ) (a b c d : ℝ)
    (hcd : c ≤ d) (hC : ContinuousOn f ([[a, b]] ×ℂ [[c, d]]))
    (hD : ∀ z ∈ Ioo (min a b) (max a b) ×ℂ Ioo c d,
      z.im ≠ 0 → DifferentiableAt ℂ f z) :
    rectangleBoundaryIntegral f a b c d = 0 := by
  by_cases hd : d ≤ 0
  · apply rectangleBoundaryIntegral_eq_zero f a b c d hC
    intro z hz
    have hz' : z ∈ Ioo (min a b) (max a b) ×ℂ Ioo c d := by
      simpa only [min_eq_left hcd, max_eq_right hcd] using hz
    exact hD z hz' (ne_of_lt (hz'.2.2.trans_le hd))
  · by_cases hc : 0 ≤ c
    · apply rectangleBoundaryIntegral_eq_zero f a b c d hC
      intro z hz
      have hz' : z ∈ Ioo (min a b) (max a b) ×ℂ Ioo c d := by
        simpa only [min_eq_left hcd, max_eq_right hcd] using hz
      exact hD z hz' (ne_of_gt (hc.trans_lt hz'.2.1))
    · exact rectangleBoundaryIntegral_eq_zero_crossing f a b c d
        (le_of_not_ge hc) (le_of_not_ge hd) hC hD

/-- Cauchy cancellation across a continuous real-axis seam, for arbitrary
rectangle orientations and without differentiability on the seam itself. -/
theorem rectangleBoundaryIntegral_eq_zero_off_real (f : ℂ → ℂ) (a b c d : ℝ)
    (hC : ContinuousOn f ([[a, b]] ×ℂ [[c, d]]))
    (hD : ∀ z ∈ Ioo (min a b) (max a b) ×ℂ Ioo (min c d) (max c d),
      z.im ≠ 0 → DifferentiableAt ℂ f z) :
    rectangleBoundaryIntegral f a b c d = 0 := by
  by_cases hcd : c ≤ d
  · apply rectangleBoundaryIntegral_eq_zero_off_real_ordered f a b c d hcd hC
    simpa only [min_eq_left hcd, max_eq_right hcd] using hD
  · have hdc : d ≤ c := le_of_not_ge hcd
    have hrev : rectangleBoundaryIntegral f a b d c = 0 := by
      apply rectangleBoundaryIntegral_eq_zero_off_real_ordered f a b d c hdc
      · simpa only [uIcc_comm] using hC
      · simpa only [min_eq_right hdc, max_eq_left hdc] using hD
    rw [rectangleBoundaryIntegral_swap_vertical f a b d c, hrev, neg_zero]

/-- A continuous function holomorphic off the real axis is holomorphic across
that axis. All rectangle and integrability conditions of Morera are derived
above, so no integral-cancellation oracle is part of the statement. -/
theorem differentiableOn_of_continuousOn_off_real {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hC : ContinuousOn f U)
    (hD : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ f z) :
    DifferentiableOn ℂ f U := by
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_, hC⟩
  intro z w hrect
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  have h := rectangleBoundaryIntegral_eq_zero_off_real f z.re w.re z.im w.im
    (hC.mono hrect) (by
      intro x hx hxi
      apply hD x (hrect ?_) hxi
      exact ⟨Ioo_subset_Icc_self hx.1, Ioo_subset_Icc_self hx.2⟩)
  simpa only [rectangleBoundaryIntegral, smul_eq_mul] using h

end
end CGLMPBounds.Hardy
