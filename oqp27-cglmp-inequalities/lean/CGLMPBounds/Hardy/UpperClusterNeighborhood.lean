module

public import CGLMPBounds.Hardy.UpperClusterCircle
public import Mathlib.Analysis.Normed.Algebra.Spectrum

@[expose] public section


/-!
# A fixed upper-cluster contour on a neighborhood of the pencil parameter

Mathlib's upper hemicontinuity of the spectrum keeps nearby spectra inside
the union of the selected upper disk and the lower half-plane. Consequently
one fixed circle computes the upper-cluster trace throughout a neighborhood.
No continuously enumerated eigenvalues or simple-spectrum condition is used.

This prepares differentiation under the fixed contour integral. It does not
yet prove that differentiation step or the C.8 boundary/moment formula.
-/

open Complex Metric Set Filter
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

lemma upper_circle_closedBall_im_nonneg {T : ℝ} {a : ℂ}
    (ha : a ∈ closedBall ((T : ℂ) * Complex.I) T) : 0 ≤ a.im := by
  have hnorm : ‖a - (T : ℂ) * Complex.I‖ ≤ T := mem_closedBall_iff_norm.mp ha
  have hi := Complex.abs_im_le_norm (a - (T : ℂ) * Complex.I)
  have he : (a - (T : ℂ) * Complex.I).im = a.im - T := by simp
  rw [he] at hi
  linarith [neg_le_abs (a.im - T)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- The actual spectral map of the pencil is upper hemicontinuous. -/
lemma upperHemicontinuousAt_pencil_spectrum (H Y : Matrix ι ι ℂ) (z : ℂ) :
    UpperHemicontinuousAt (fun w => spectrum ℂ (traceDensityPencil H Y w)) z := by
  exact ((upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).upperHemicontinuousAt
    (traceDensityPencil H Y z)).comp (analyticAt_traceDensityPencil H Y z).continuousAt

/-- A fixed circle remains separating and selects exactly the upper roots
for every sufficiently nearby pencil parameter. -/
theorem eventually_pencil_upper_circle_separates {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {z : ℂ} (hz : 0 < z.im) :
    let R := upperClusterRadius (traceDensityPencil H Y z).charpoly.roots
    ∀ᶠ w in 𝓝 z, ∀ a ∈ (traceDensityPencil H Y w).charpoly.roots,
      a ∉ sphere ((R : ℂ) * Complex.I) R ∧
        (a ∈ ball ((R : ℂ) * Complex.I) R ↔ 0 < a.im) := by
  let R := upperClusterRadius (traceDensityPencil H Y z).charpoly.roots
  let U : Set ℂ := ball ((R : ℂ) * Complex.I) R ∪ {a : ℂ | a.im < 0}
  have hU : IsOpen U := isOpen_ball.union (isOpen_lt Complex.continuous_im continuous_const)
  have hsub : spectrum ℂ (traceDensityPencil H Y z) ⊆ U := by
    intro a ha
    have hr : a ∈ (traceDensityPencil H Y z).charpoly.roots :=
      (Polynomial.mem_roots (traceDensityPencil H Y z).charpoly_monic.ne_zero).2
        (Matrix.mem_spectrum_iff_isRoot_charpoly.mp ha)
    have hn := pencil_roots_im_ne_zero hH hY hdet hz a hr
    by_cases hi : 0 < a.im
    · exact Or.inl ((upperClusterRadius_separates _
        (pencil_roots_im_ne_zero hH hY hdet hz) hr).2.mpr hi)
    · exact Or.inr (lt_of_le_of_ne (le_of_not_gt hi) hn)
  have he := (upperHemicontinuousAt_pencil_spectrum H Y z).forall_isOpen U hU hsub
  filter_upwards [he] with w hw
  intro a ha
  have hau : a ∈ U := hw
    (Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha))
  rcases hau with hin | hlow
  · refine ⟨?_, ⟨fun _ => upper_circle_ball_subset hin, fun _ => hin⟩⟩
    intro hs
    have hdlt : dist a ((R : ℂ) * Complex.I) < R := hin
    have hdeq := Metric.mem_sphere.mp hs
    linarith
  · have hout : a ∉ closedBall ((R : ℂ) * Complex.I) R := by
      intro hc
      have hnonneg := upper_circle_closedBall_im_nonneg hc
      exact (not_lt_of_ge hnonneg) hlow
    refine ⟨fun hs => hout (sphere_subset_closedBall hs), ⟨?_, ?_⟩⟩
    · intro hb
      exact False.elim (hout (ball_subset_closedBall hb))
    · intro hi
      exact False.elim ((not_lt_of_ge hi.le) hlow)

/-- The source upper-cluster trace agrees locally with one fixed, genuine
normalized contour integral. This is stronger than choosing a new contour
independently at every parameter. -/
theorem pencil_upperClusterTrace_eventuallyEq_fixed_circle {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {z : ℂ} (hz : 0 < z.im) :
    let R := upperClusterRadius (traceDensityPencil H Y z).charpoly.roots
    (fun w => upperClusterTrace (traceDensityPencil H Y w)) =ᶠ[𝓝 z]
      (fun w => (∮ ζ in C((R : ℂ) * Complex.I, R), pencilTraceIntegrand H Y ζ w) /
        (2 * Real.pi * Complex.I : ℂ)) := by
  let R := upperClusterRadius (traceDensityPencil H Y z).charpoly.roots
  filter_upwards [eventually_pencil_upper_circle_separates hH hY hdet hz] with w hw
  rw [pencilTrace_circleIntegral_eq_cluster]
  symm
  exact circleClusterTrace_eq_upperClusterTrace _ (upperClusterRadius_pos _).le
    (fun a ha => (hw a ha).1) (fun a ha => (hw a ha).2)

/-- Every point on that fixed contour remains in the actual resolvent set
throughout a common parameter neighborhood. -/
theorem eventually_pencil_fixed_circle_resolvent {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {z : ℂ} (hz : 0 < z.im) :
    let R := upperClusterRadius (traceDensityPencil H Y z).charpoly.roots
    ∀ᶠ w in 𝓝 z, ∀ ζ ∈ sphere ((R : ℂ) * Complex.I) R,
      ζ ∉ spectrum ℂ (traceDensityPencil H Y w) := by
  filter_upwards [eventually_pencil_upper_circle_separates hH hY hdet hz] with w hw
  intro ζ hζ
  exact circle_not_mem_spectrum_of_root_separation _
    (fun a ha => (hw a ha).1) hζ

end
end CGLMPBounds.Hardy
