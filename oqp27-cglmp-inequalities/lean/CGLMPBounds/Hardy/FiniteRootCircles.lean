module

public import Mathlib

@[expose] public section


/-! A finite set in an open complex domain admits uniformly sized separated
closed disks. Points near that finite set lie inside exactly one disk and on
none of the boundary circles. This supplies actual local spectral contours. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Metric Filter
open scoped Topology

theorem finite_exists_separated_closedBalls (s : Finset ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hs : ∀ a ∈ s, a ∈ U) :
    ∃ R : ℝ, 0 < R ∧ (∀ a ∈ s, closedBall a R ⊆ U) ∧
      ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 3 * R < dist a b := by
  have hc : ∀ᶠ R : ℝ in 𝓝 0, ∀ a ∈ s, closedBall a R ⊆ U := by
    apply (eventually_all_finset s).mpr
    intro a ha
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hs a ha))
    filter_upwards [gt_mem_nhds hr] with R hR
    exact (closedBall_subset_ball hR).trans hsub
  have hd : ∀ᶠ R : ℝ in 𝓝 0, ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 3 * R < dist a b := by
    apply (eventually_all_finset s).mpr
    intro a ha
    apply (eventually_all_finset s).mpr
    intro b hb
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall (fun R hne => (hne hab).elim)
    · have hpos : 0 < dist a b := dist_pos.mpr hab
      exact ((continuousAt_const.mul continuousAt_id).eventually_lt continuousAt_const
        (by simpa using hpos)).mono (fun _ h _ => h)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hc.and hd)
  have hm : ε / 2 ∈ ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  exact ⟨ε / 2, half_pos hε, (hsub hm).1, (hsub hm).2⟩

theorem unique_circle_of_near_finite_set (s : Finset ℂ) {R : ℝ} (hR : 0 < R)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 3 * R < dist a b)
    {z : ℂ} (hz : ∃ a ∈ s, z ∈ ball a (R / 2)) :
    (∃ a ∈ s, z ∈ ball a R ∧ ∀ b ∈ s, z ∈ ball b R → b = a) ∧
      ∀ a ∈ s, z ∉ sphere a R := by
  obtain ⟨a, ha, hza⟩ := hz
  have hza' : dist z a < R / 2 := hza
  have hfull : z ∈ ball a R := by change dist z a < R; linarith
  constructor
  · refine ⟨a, ha, hfull, ?_⟩
    intro b hb hzb
    by_contra hba
    have hl := hsep a ha b hb (Ne.symm hba)
    have ht := dist_triangle a z b
    have hzb' : dist z b < R := hzb
    rw [dist_comm a z] at ht
    linarith
  · intro b hb hzb
    by_cases hab : a = b
    · subst b
      have he := Metric.mem_sphere.mp hzb
      linarith
    · have hl := hsep a ha b hb hab
      have ht := dist_triangle a z b
      have he := Metric.mem_sphere.mp hzb
      rw [dist_comm a z] at ht
      linarith

end
end CGLMPBounds.Hardy
