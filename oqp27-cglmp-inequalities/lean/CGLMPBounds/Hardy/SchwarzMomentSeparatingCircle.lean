module

public import CGLMPBounds.Hardy.SchwarzMomentPositiveTrace

@[expose] public section


/-! C.7 on any actual circle selecting the positive spectrum. The change of
contour is proved from the existing finite-pole cancellation theorem. -/

open Complex Metric Set
namespace CGLMPBounds.Hardy
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem traceDensity_moment_eq_separating_circle
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (m : ℕ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hsep : ∀ a ∈ H.charpoly.roots, a ∉ sphere c R)
    (hselect : ∀ a ∈ H.charpoly.roots, a ∈ ball c R ↔ 0 < a.re) :
    ((∫ y : ℝ, y ^ m * traceDensity H Y y : ℝ) : ℂ) =
      (1 / ((m + 2 : ℕ) : ℂ)) *
        (∮ z in C(c, R), z ^ m * Matrix.trace ((resolvent H z * Y) ^ (m + 2))) /
          (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by
  let P := negativeClusterRadius H.charpoly.roots
  have hP : 0 < P := negativeClusterRadius_pos _
  have haxis : ∀ a ∈ H.charpoly.roots, a.re ≠ 0 :=
    fun a ha => hermitian_root_re_ne_zero hH hdet ha
  have hpos (a : ℂ) (ha : a ∈ H.charpoly.roots) :=
    positiveClusterRadius_separates H.charpoly.roots haxis ha
  have hneg (a : ℂ) (ha : a ∈ H.charpoly.roots) :=
    negativeClusterRadius_separates H.charpoly.roots haxis ha
  have hpart : ∀ a ∈ H.charpoly.roots, a ∈ ball c R ↔ a ∉ ball (-(P : ℂ)) P := by
    intro a ha
    rw [hselect a ha, (hneg a ha).2]
    constructor
    · intro hp hn
      linarith
    · intro hn
      exact lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (haxis a ha))
  have hpart' : ∀ a ∈ H.charpoly.roots,
      a ∈ ball (P : ℂ) P ↔ a ∉ ball (-(P : ℂ)) P := by
    intro a ha
    rw [(hpos a ha).2, ← hselect a ha]
    exact hpart a ha
  have hc := weighted_resolvent_circle_partition_sum_zero H Y (by omega : 2 ≤ m + 2)
    hR hP.le hsep (fun a ha => (hneg a ha).1) hpart
  have hp := weighted_resolvent_circle_partition_sum_zero H Y (by omega : 2 ≤ m + 2)
    hP.le hP.le (fun a ha => (hpos a ha).1) (fun a ha => (hneg a ha).1) hpart'
  have he : (∮ z in C((P : ℂ), P),
      z ^ m * Matrix.trace ((resolvent H z * Y) ^ (m + 2))) =
      ∮ z in C(c, R), z ^ m * Matrix.trace ((resolvent H z * Y) ^ (m + 2)) := by
    simp only [Nat.add_sub_cancel] at hc hp
    linear_combination hp - hc
  rw [traceDensity_moment_eq_exteriorTaylorCoefficient hH hY hdet m,
    exteriorTaylorCoefficient_eq_positive_resolvent_power Y hH hdet (by omega)]
  simpa only [Nat.add_sub_cancel, P, he]

end
end CGLMPBounds.Hardy
