module

public import CGLMPBounds.Hardy.SchwarzRootScaling

@[expose] public section


/-!
# The actual g/q exterior identity on the positive imaginary axis

Spectral upper hemicontinuity identifies q with the strictly left-half-plane
root sum near zero. The exact characteristic-root scaling formula then proves
`g(it)=-it*q((it)⁻¹)` for every sufficiently large positive real t. This is an
identity between the actual source functions, without any target identity as
a hypothesis. It is a first step toward the upper exterior identity; extending
it to that connected domain by holomorphic uniqueness is still separate.
-/

open Complex Metric Set Filter
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

lemma negative_circle_ball_re_neg {T : ℝ} {a : ℂ}
    (ha : a ∈ ball (-(T : ℂ)) T) : a.re < 0 := by
  have hnorm : ‖a - (-(T : ℂ))‖ < T := mem_ball_iff_norm.mp ha
  have hr := Complex.abs_re_le_norm (a - (-(T : ℂ)))
  have he : (a - (-(T : ℂ))).re = a.re + T := by simp
  rw [he] at hr
  linarith [le_abs_self (a.re + T)]

lemma negative_circle_closedBall_re_nonpos {T : ℝ} {a : ℂ}
    (ha : a ∈ closedBall (-(T : ℂ)) T) : a.re ≤ 0 := by
  have hnorm : ‖a - (-(T : ℂ))‖ ≤ T := mem_closedBall_iff_norm.mp ha
  have hr := Complex.abs_re_le_norm (a - (-(T : ℂ)))
  have he : (a - (-(T : ℂ))).re = a.re + T := by simp
  rw [he] at hr
  linarith [le_abs_self (a.re + T)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem eventually_exterior_negative_circle_separates {H : Matrix ι ι ℂ}
    (Y : Matrix ι ι ℂ) (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    let R := negativeClusterRadius H⁻¹.charpoly.roots
    ∀ᶠ w in 𝓝 (0 : ℂ), ∀ a ∈ (exteriorPencil H Y w).charpoly.roots,
      a ∉ sphere (-(R : ℂ)) R ∧ (a ∈ ball (-(R : ℂ)) R ↔ a.re < 0) := by
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  let U : Set ℂ := ball (-(R : ℂ)) R ∪ {a : ℂ | 0 < a.re}
  have hU : IsOpen U := isOpen_ball.union (isOpen_lt continuous_const Complex.continuous_re)
  have hsub : spectrum ℂ (exteriorPencil H Y 0) ⊆ U := by
    rw [exteriorPencil_zero]
    intro a ha
    have hr : a ∈ H⁻¹.charpoly.roots :=
      (Polynomial.mem_roots H⁻¹.charpoly_monic.ne_zero).2
        (Matrix.mem_spectrum_iff_isRoot_charpoly.mp ha)
    have hn := hermitian_inverse_root_re_ne_zero hH hdet hr
    by_cases hi : a.re < 0
    · exact Or.inl ((negativeClusterRadius_separates _
        (fun b hb => hermitian_inverse_root_re_ne_zero hH hdet hb) hr).2.mpr hi)
    · exact Or.inr (lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hn))
  have hhemi : UpperHemicontinuousAt
      (fun w => spectrum ℂ (exteriorPencil H Y w)) 0 :=
    ((upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).upperHemicontinuousAt
      (exteriorPencil H Y 0)).comp (analyticAt_exteriorPencil H Y 0).continuousAt
  filter_upwards [hhemi.forall_isOpen U hU hsub] with w hw
  intro a ha
  have hau : a ∈ U := hw
    (Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha))
  rcases hau with hin | hright
  · refine ⟨?_, ⟨fun _ => negative_circle_ball_re_neg hin, fun _ => hin⟩⟩
    intro hs
    have hdlt : dist a (-(R : ℂ)) < R := hin
    have hdeq := Metric.mem_sphere.mp hs
    linarith
  · have hout : a ∉ closedBall (-(R : ℂ)) R := by
      intro hc
      exact (not_lt_of_ge (negative_circle_closedBall_re_nonpos hc)) hright
    refine ⟨fun hs => hout (sphere_subset_closedBall hs), ⟨?_, ?_⟩⟩
    · intro hb
      exact False.elim (hout (ball_subset_closedBall hb))
    · intro hi
      exact False.elim ((not_lt_of_ge hi.le) hright)

/-- Near zero the literal fixed contour is precisely the actual negative
root cluster. This local equality does not assert global selector analyticity. -/
theorem exteriorClusterQ_eventuallyEq_negativeClusterTrace {H : Matrix ι ι ℂ}
    (Y : Matrix ι ι ℂ) (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    exteriorClusterQ H Y =ᶠ[𝓝 (0 : ℂ)]
      (fun w => negativeClusterTrace (exteriorPencil H Y w)) := by
  classical
  filter_upwards [eventually_exterior_negative_circle_separates Y hH hdet] with w hw
  unfold exteriorClusterQ negativeClusterTrace
  rw [circleClusterTrace_eq_root_sum _ (negativeClusterRadius_pos _).le
    (fun a ha => (hw a ha).1)]
  apply congrArg (fun t : ℂ => t / (Fintype.card ι : ℂ))
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro a ha
  rw [(hw a ha).2]

/-- The source exterior identity, already valid on an unbounded portion of
the positive imaginary axis with exact normalization and algebraic multiplicity. -/
theorem exists_upperClusterTrace_eq_exterior_on_imaginary {H : Matrix ι ι ℂ}
    (Y : Matrix ι ι ℂ) (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R < t →
      upperClusterTrace (traceDensityPencil H Y ((t : ℂ) * Complex.I)) =
        (-(t : ℂ) * Complex.I) * exteriorClusterQ H Y (((t : ℂ) * Complex.I)⁻¹) := by
  obtain ⟨ε, hε, hq⟩ := Metric.eventually_nhds_iff_ball.mp
    (exteriorClusterQ_eventuallyEq_negativeClusterTrace Y hH hdet)
  refine ⟨max 1 ε⁻¹, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro t ht
  have htpos : 0 < t := lt_trans
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)) ht
  have htε : ε⁻¹ < t := (le_max_right _ _).trans_lt ht
  have hmul : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
  have hlt := mul_lt_mul_of_pos_left htε hε
  rw [hmul] at hlt
  have hdiv : 1 / t < ε := (div_lt_iff₀ htpos).mpr (by nlinarith)
  have hnorm : ‖((t : ℂ) * Complex.I)⁻¹‖ = 1 / t := by
    simp [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, one_div]
  have hmem : ((t : ℂ) * Complex.I)⁻¹ ∈ ball (0 : ℂ) ε := by
    simpa only [mem_ball_iff_norm, sub_zero, hnorm] using hdiv
  have htn : (t : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast htpos.ne') Complex.I_ne_zero
  rw [traceDensityPencil_eq_exterior_smul H Y htn, ← neg_mul,
    upperClusterTrace_neg_imag_smul _ t htpos, hq _ hmem]

end
end CGLMPBounds.Hardy
