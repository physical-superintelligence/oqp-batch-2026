module

public import CGLMPBounds.Hardy.SchwarzNegativeCoefficients
public import CGLMPBounds.Hardy.SchwarzExteriorImaginary
public import Mathlib.Data.Finset.DenselyOrdered

@[expose] public section


/-! A genuine deformation away from zero before the C.7 contour inversion.
The original exterior q circle touches zero. Finite strict root separation
provides a smaller concentric circle; the annulus contains no spectral point.
Cauchy's actual annulus theorem transfers the coefficient integral to this
new circle, whose entire closed disk avoids zero. The original definition of
q and its analytic germ remain unchanged. No inversion formula is assumed. -/

open Complex Filter Set Metric
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

lemma exists_smaller_negative_circle (s : Multiset ℂ)
    (haxis : ∀ a ∈ s, a.re ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < negativeClusterRadius s ∧
      ∀ a ∈ s, a ∉ closedBall (-(negativeClusterRadius s : ℂ)) (negativeClusterRadius s) ∨
        a ∈ ball (-(negativeClusterRadius s : ℂ)) r := by
  classical
  let R := negativeClusterRadius s
  let L : Finset ℝ := insert 0
    ((s.toFinset.filter (fun a => a.re < 0)).image (fun a => dist a (-(R : ℂ))))
  have hL : ∀ x ∈ L, ∀ y ∈ ({R} : Finset ℝ), x < y := by
    intro x hx y hy
    have hyr : y = R := Finset.mem_singleton.mp hy
    subst y
    rcases Finset.mem_insert.mp hx with hzero | hd
    · subst x
      exact negativeClusterRadius_pos s
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨ha, hneg⟩ := Finset.mem_filter.mp ha
      exact (negativeClusterRadius_separates s haxis
        (Multiset.mem_toFinset.mp ha)).2.mpr hneg
  obtain ⟨r, hrL, hrR⟩ := Finset.exists_between
    (show L.Nonempty from ⟨0, Finset.mem_insert_self _ _⟩)
    (Finset.singleton_nonempty R) hL
  refine ⟨r, hrL 0 (Finset.mem_insert_self _ _),
    hrR R (Finset.mem_singleton_self R), ?_⟩
  intro a ha
  by_cases hneg : a.re < 0
  · right
    exact hrL _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ha, hneg⟩, rfl⟩))
  · left
    have hpos : 0 < a.re := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm (haxis a ha))
    intro hc
    exact (not_lt_of_ge (negative_circle_closedBall_re_nonpos hc)) hpos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- There is a genuine smaller contour enclosing every negative base root,
excluding all other roots and zero, with a completely root-free annulus. -/
theorem exists_safe_negative_inverse_circle {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    let R := negativeClusterRadius H⁻¹.charpoly.roots
    ∃ r : ℝ, 0 < r ∧ r < R ∧ (0 : ℂ) ∉ closedBall (-(R : ℂ)) r ∧
      (∀ a ∈ H⁻¹.charpoly.roots,
        a ∉ sphere (-(R : ℂ)) r ∧ (a ∈ ball (-(R : ℂ)) r ↔ a.re < 0)) ∧
      (∀ ζ ∈ closedBall (-(R : ℂ)) R \ ball (-(R : ℂ)) r,
        ζ ∉ spectrum ℂ H⁻¹) := by
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  obtain ⟨r, hr0, hrR, hroots⟩ := exists_smaller_negative_circle H⁻¹.charpoly.roots
    (fun a ha => hermitian_inverse_root_re_ne_zero hH hdet ha)
  refine ⟨r, hr0, hrR, ?_, ?_, ?_⟩
  · intro hzero
    have hz : R ≤ r := by
      simpa only [Metric.mem_closedBall, dist_zero_left, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (negativeClusterRadius_pos _)] using hzero
    linarith
  · intro a ha
    rcases hroots a ha with hout | hin
    · refine ⟨?_, ⟨?_, ?_⟩⟩
      · intro hs
        apply hout
        exact (sphere_subset_closedBall hs).trans hrR.le
      · intro hb
        exact False.elim (hout ((ball_subset_closedBall hb).trans hrR.le))
      · intro hn
        exact False.elim (hout (ball_subset_closedBall
          ((negativeClusterRadius_separates _
            (fun b hb => hermitian_inverse_root_re_ne_zero hH hdet hb) ha).2.mpr hn)))
    · refine ⟨?_, ⟨?_, fun _ => hin⟩⟩
      · intro hs
        have hlt : dist a (-(R : ℂ)) < r := hin
        have heq := Metric.mem_sphere.mp hs
        linarith
      · intro _
        exact negative_circle_ball_re_neg (show a ∈ ball (-(R : ℂ)) R from hin.trans hrR)
  · intro ζ hζ hs
    have hr : ζ ∈ H⁻¹.charpoly.roots :=
      (Polynomial.mem_roots H⁻¹.charpoly_monic.ne_zero).2
        (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hs)
    rcases hroots ζ hr with hout | hin
    · exact hout hζ.1
    · exact hζ.2 hin

/-- The negative coefficient formula on an actual contour whose whole disk
avoids zero. The annulus identity is proved, not supplied as a premise. -/
theorem exteriorTaylorCoefficient_eq_safe_negative_resolvent_power
    {H : Matrix ι ι ℂ} (Y : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hdet : IsUnit H.det) {n : ℕ} (hn : 0 < n) :
    let R := negativeClusterRadius H⁻¹.charpoly.roots
    ∃ r : ℝ, 0 < r ∧ r < R ∧ (0 : ℂ) ∉ closedBall (-(R : ℂ)) r ∧
      (∀ a ∈ H⁻¹.charpoly.roots,
        a ∉ sphere (-(R : ℂ)) r ∧ (a ∈ ball (-(R : ℂ)) r ↔ a.re < 0)) ∧
      exteriorTaylorCoefficient H Y n =
        ((-1 : ℂ) ^ n / (n : ℂ)) *
          (∮ ζ in C((-(R : ℂ)), r), Matrix.trace ((Ring.inverse (ζ • H - 1) * Y) ^ n)) /
            (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  obtain ⟨r, hr0, hrR, hzero, hselect, hsep⟩ := exists_safe_negative_inverse_circle hH hdet
  refine ⟨r, hr0, hrR, hzero, hselect, ?_⟩
  let F : ℂ → ℂ := fun ζ => Matrix.trace ((Ring.inverse (ζ • H - 1) * Y) ^ n)
  have hF : F = fun ζ => Matrix.trace ((resolvent H⁻¹ ζ * H⁻¹ * Y) ^ n) := by
    funext ζ
    rw [inverse_inverse_pencil_resolvent H hdet ζ]
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have hc : ContinuousOn F (closedBall (-(R : ℂ)) R \ ball (-(R : ℂ)) r) := by
    rw [hF]
    exact tr.continuous.comp_continuousOn
      ((((continuousOn_matrix_resolvent H⁻¹ hsep).mul continuousOn_const).mul
        continuousOn_const).pow n)
  have hd : ∀ ζ ∈ (ball (-(R : ℂ)) R \ closedBall (-(R : ℂ)) r) \ (∅ : Set ℂ),
      DifferentiableAt ℂ F ζ := by
    intro ζ hζ
    have hzann : ζ ∈ closedBall (-(R : ℂ)) R \ ball (-(R : ℂ)) r :=
      ⟨ball_subset_closedBall hζ.1.1, fun hb => hζ.1.2 (ball_subset_closedBall hb)⟩
    rw [hF]
    have hres := (hasDerivAt_matrix_resolvent H⁻¹ (hsep ζ hzann)).differentiableAt
    have hprod := (hres.mul_const H⁻¹).mul_const Y
    exact tr.differentiableAt.comp ζ (hprod.pow n)
  have heq := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr0 hrR.le Set.countable_empty hc hd
  rw [exteriorTaylorCoefficient_eq_negative_resolvent_power Y hH hdet hn]
  change ((-1 : ℂ) ^ n / (n : ℂ)) * (∮ ζ in C((-(R : ℂ)), R), F ζ) /
      (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) = _
  rw [heq]

end
end CGLMPBounds.Hardy
