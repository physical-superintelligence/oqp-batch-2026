module

public import CGLMPBounds.Hardy.FiniteRootCircles
public import CGLMPBounds.Hardy.HolomorphicCircleTrace

@[expose] public section


/-! Analyticity of the actual normalized characteristic-root sum along a
holomorphic matrix family. Finite fixed circles are constructed around the
distinct base roots; repeated roots remain in the multiset calculations.
Spectral upper hemicontinuity keeps all nearby roots in exactly one circle. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Complex Matrix Set Metric Filter
open scoped Topology Matrix.Norms.Operator Classical
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma finite_circle_root_sum (s : Finset ℂ) (P : Multiset ℂ) (f : ℂ → ℂ) (R : ℝ)
    (hunique : ∀ z ∈ P, ∃ a ∈ s, z ∈ ball a R ∧
      ∀ b ∈ s, z ∈ ball b R → b = a) :
    (∑ a ∈ s, (P.map (fun z => if z ∈ ball a R then f z else 0)).sum) =
      (P.map f).sum := by
  revert hunique
  induction P using Multiset.induction_on with
  | empty => intro _; simp
  | @cons z P ih =>
    intro hunique
    obtain ⟨a, ha, hza, huniq⟩ := hunique z (Multiset.mem_cons_self _ _)
    have hzsum : (∑ b ∈ s, if z ∈ ball b R then f z else 0) = f z := by
      rw [Finset.sum_eq_single a]
      · simp only [if_pos hza]
      · intro b hb hba
        exact if_neg (fun hz => hba (huniq b hb hz))
      · exact fun h => (h ha).elim
    simp only [Multiset.map_cons, Multiset.sum_cons, Finset.sum_add_distrib, hzsum]
    rw [ih (fun w hw => hunique w (Multiset.mem_cons_of_mem hw))]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem analyticAt_normalizedSpectralTrace
    {M : ℂ → Matrix ι ι ℂ} {f : ℂ → ℂ} {z : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hM : AnalyticAt ℂ M z) (hf : AnalyticOnNhd ℂ f U)
    (hspec : spectrum ℂ (M z) ⊆ U) :
    AnalyticAt ℂ (fun w => normalizedSpectralTrace f (M w)) z := by
  classical
  let s := (M z).charpoly.roots.toFinset
  have hs : ∀ a ∈ s, a ∈ U := by
    intro a ha
    exact hspec (Matrix.mem_spectrum_of_isRoot_charpoly
      (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp ha)))
  obtain ⟨R, hR, hballs, hseparated⟩ := finite_exists_separated_closedBalls s hU hs
  let V : Set ℂ := ⋃ a ∈ (↑s : Set ℂ), ball a (R / 2)
  have hV : IsOpen V := isOpen_biUnion (fun _ _ => isOpen_ball)
  have hin : spectrum ℂ (M z) ⊆ V := by
    intro a ha
    have har : a ∈ (M z).charpoly.roots :=
      (Polynomial.mem_roots (M z).charpoly_monic.ne_zero).mpr
        (Matrix.mem_spectrum_iff_isRoot_charpoly.mp ha)
    exact mem_iUnion₂.mpr ⟨a, Multiset.mem_toFinset.mpr har, mem_ball_self (half_pos hR)⟩
  have hh : UpperHemicontinuousAt (fun w => spectrum ℂ (M w)) z :=
    ((upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).upperHemicontinuousAt (M z)).comp
      hM.continuousAt
  have he : ∀ᶠ w in 𝓝 z, ∀ a ∈ (M w).charpoly.roots,
      (∃ b ∈ s, a ∈ ball b R ∧ ∀ c ∈ s, a ∈ ball c R → c = b) ∧
        ∀ b ∈ s, a ∉ sphere b R := by
    filter_upwards [hh.forall_isOpen V hV hin] with w hw
    intro a ha
    have hau := hw (Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha))
    apply unique_circle_of_near_finite_set s hR hseparated
    obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp hau
    exact ⟨b, hb, hab⟩
  let T : ℂ → ℂ := fun w => ∑ a ∈ s,
    (∮ ζ in C(a, R), f ζ * Matrix.trace (resolvent (M w) ζ)) /
      (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ)
  have hT : AnalyticAt ℂ T z := by
    apply Finset.analyticAt_fun_sum
    intro a ha
    apply analyticAt_holomorphic_circle_trace hR.le hM
    · intro ζ hζ
      exact hf ζ (hballs a ha (sphere_subset_closedBall hζ))
    · intro ζ hζ
      exact circle_not_mem_spectrum_of_root_separation (M z)
        (fun b hb => (he.self_of_nhds b hb).2 a ha) hζ
  have heq : (fun w => normalizedSpectralTrace f (M w)) =ᶠ[𝓝 z] T := by
    filter_upwards [he] with w hw
    unfold normalizedSpectralTrace T
    have hcircle : (∑ a ∈ s,
        (∮ ζ in C(a, R), f ζ * Matrix.trace (resolvent (M w) ζ)) /
          (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ)) =
        ∑ a ∈ s, ( (M w).charpoly.roots.map
          (fun b => if b ∈ ball a R then f b else 0)).sum / (Fintype.card ι : ℂ) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact circleIntegral_holomorphic_resolvent_trace (M w) hR.le
        (hf.mono (hballs a ha)) (fun b hb => (hw b hb).2 a ha)
    rw [hcircle, ← Finset.sum_div, finite_circle_root_sum s (M w).charpoly.roots f R
      (fun b hb => (hw b hb).1)]
  exact hT.congr heq.symm

end
end CGLMPBounds.Hardy
