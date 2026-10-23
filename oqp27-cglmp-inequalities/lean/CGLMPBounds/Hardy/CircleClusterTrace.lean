module

public import CGLMPBounds.Defs.HardyExterior
public import CGLMPBounds.Hardy.TraceResolvent
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section


/-!
# Contour selection of characteristic roots with algebraic multiplicity

This is the next contour bridge in the proof of Lemma C.3, preceding C.8.
The actual trace-resolvent integral selects exactly the roots inside a circle.
The calculation retains the full characteristic-root multiset and therefore
does not require distinct roots or a diagonalizable matrix.
-/

open Complex Metric Set
open scoped Real

namespace CGLMPBounds.Hardy
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma circleIntegral_sub_inv_of_outside {c a : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (ha : a ∉ closedBall c R) :
    (∮ ζ in C(c, R), (ζ - a)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hR (s := (∅ : Set ℂ)) Set.countable_empty
  · exact (continuousOn_id.sub continuousOn_const).inv₀
      (fun ζ hζ => sub_ne_zero.mpr (ne_of_mem_of_not_mem hζ ha))
  · intro ζ hζ
    exact (differentiableAt_id.sub_const a).inv
      (sub_ne_zero.mpr (ne_of_mem_of_not_mem (ball_subset_closedBall hζ.1) ha))

lemma rootFraction_circleIntegrable {c a : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (ha : a ∉ sphere c R) :
    CircleIntegrable (fun ζ => a / (ζ - a)) c R := by
  have hc : ContinuousOn (fun ζ : ℂ => a * (ζ - a)⁻¹) (sphere c R) :=
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀
      (fun ζ hζ => sub_ne_zero.mpr (ne_of_mem_of_not_mem hζ ha)))
  simpa only [div_eq_mul_inv] using hc.circleIntegrable hR

/-- The scalar residue calculation, including roots outside the contour. -/
theorem circleIntegral_rootFraction {c a : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (ha : a ∉ sphere c R) :
    (∮ ζ in C(c, R), a / (ζ - a)) =
      (2 * Real.pi * Complex.I : ℂ) * (if a ∈ ball c R then a else 0) := by
  classical
  simp only [div_eq_mul_inv]
  rw [circleIntegral.integral_const_mul]
  by_cases hin : a ∈ ball c R
  · rw [if_pos hin, circleIntegral.integral_sub_inv_of_mem_ball hin]
    ring
  · have hout : a ∉ closedBall c R := by
      intro hclosed
      apply ha
      apply Metric.mem_sphere.mpr
      have hn : ¬dist a c < R := hin
      have hc : dist a c ≤ R := hclosed
      exact le_antisymm hc (le_of_not_gt hn)
    rw [if_neg hin, circleIntegral_sub_inv_of_outside hR hout]
    simp

lemma rootFractionSum_circleIntegrable (s : Multiset ℂ) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hsep : ∀ a ∈ s, a ∉ sphere c R) :
    CircleIntegrable (fun ζ => (s.map (fun a => a / (ζ - a))).sum) c R := by
  revert hsep
  induction s using Multiset.induction_on with
  | empty => intro _; simpa using circleIntegrable_const (0 : ℂ) c R
  | @cons a s ih =>
    intro hsep
    have ha := rootFraction_circleIntegrable hR (hsep a (Multiset.mem_cons_self _ _))
    have hs := ih (fun b hb => hsep b (Multiset.mem_cons_of_mem hb))
    simp only [Multiset.map_cons, Multiset.sum_cons]
    change CircleIntegrable ((fun ζ : ℂ => a / (ζ-a)) +
      (fun ζ : ℂ => (s.map (fun b => b / (ζ-b))).sum)) c R
    exact ha.add hs

/-- Integrating the finite multiset of fractions counts every root with its
algebraic multiplicity. No simple-spectrum hypothesis enters the calculation. -/
theorem circleIntegral_rootFractionSum (s : Multiset ℂ) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hsep : ∀ a ∈ s, a ∉ sphere c R) :
    (∮ ζ in C(c, R), (s.map (fun a => a / (ζ - a))).sum) =
      (2 * Real.pi * Complex.I : ℂ) *
        (s.map (fun a => if a ∈ ball c R then a else 0)).sum := by
  classical
  revert hsep
  induction s using Multiset.induction_on with
  | empty => intro _; simp [circleIntegral]
  | @cons a s ih =>
    intro hsep
    have ha : a ∉ sphere c R := hsep a (Multiset.mem_cons_self _ _)
    have hs : ∀ b ∈ s, b ∉ sphere c R :=
      fun b hb => hsep b (Multiset.mem_cons_of_mem hb)
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [circleIntegral.integral_add (rootFraction_circleIntegrable hR ha)
      (rootFractionSum_circleIntegrable s hR hs), circleIntegral_rootFraction hR ha, ih hs]
    ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma circle_not_mem_spectrum_of_root_separation (A : Matrix ι ι ℂ)
    {c : ℂ} {R : ℝ} (hsep : ∀ a ∈ A.charpoly.roots, a ∉ sphere c R)
    {ζ : ℂ} (hζ : ζ ∈ sphere c R) : ζ ∉ spectrum ℂ A := by
  intro hs
  have hr : ζ ∈ A.charpoly.roots :=
    (Polynomial.mem_roots A.charpoly_monic.ne_zero).2
      ((Matrix.mem_spectrum_iff_isRoot_charpoly).1 hs)
  exact hsep ζ hr hζ

/-- The unnormalized matrix contour integral equals the sum of the roots in
the disk, with the exact `2*pi*i` factor. -/
theorem circleIntegral_trace_mul_resolvent (A : Matrix ι ι ℂ) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hsep : ∀ a ∈ A.charpoly.roots, a ∉ sphere c R) :
    (∮ ζ in C(c, R), Matrix.trace (A * resolvent A ζ)) =
      (2 * Real.pi * Complex.I : ℂ) *
        (A.charpoly.roots.map (fun a => if a ∈ ball c R then a else 0)).sum := by
  calc
    _ = ∮ ζ in C(c, R), (A.charpoly.roots.map (fun a => a / (ζ - a))).sum := by
      apply circleIntegral.integral_congr hR
      intro ζ hζ
      exact trace_mul_resolvent_eq_root_sum A
        (circle_not_mem_spectrum_of_root_separation A hsep hζ)
    _ = _ := circleIntegral_rootFractionSum A.charpoly.roots hR hsep

theorem circleClusterTrace_eq_root_sum (A : Matrix ι ι ℂ) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hsep : ∀ a ∈ A.charpoly.roots, a ∉ sphere c R) :
    circleClusterTrace A c R =
      (A.charpoly.roots.map (fun a => if a ∈ ball c R then a else 0)).sum /
        (Fintype.card ι : ℂ) := by
  unfold circleClusterTrace
  rw [circleIntegral_trace_mul_resolvent A hR hsep,
    mul_div_cancel_left₀ _ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])]

/-- A circle that selects exactly the upper roots computes the source `g`.
The next module constructs such a circle from the finite root multiset. -/
theorem circleClusterTrace_eq_upperClusterTrace (A : Matrix ι ι ℂ)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hsep : ∀ a ∈ A.charpoly.roots, a ∉ sphere c R)
    (hselect : ∀ a ∈ A.charpoly.roots, a ∈ ball c R ↔ 0 < a.im) :
    circleClusterTrace A c R = upperClusterTrace A := by
  classical
  rw [circleClusterTrace_eq_root_sum A hR hsep]
  unfold upperClusterTrace
  apply congrArg (fun t : ℂ => t / (Fintype.card ι : ℂ))
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro a ha
  rw [hselect a ha]

/-- Compatibility with the normalized pencil integrand already constructed
in `Resolvent.lean`; its normalization is inside the circle integral. -/
theorem pencilTrace_circleIntegral_eq_cluster (H Y : Matrix ι ι ℂ) (z c : ℂ) (R : ℝ) :
    (∮ ζ in C(c, R), pencilTraceIntegrand H Y ζ z) /
        (2 * Real.pi * Complex.I : ℂ) = circleClusterTrace (traceDensityPencil H Y z) c R := by
  unfold pencilTraceIntegrand pencilResolvent circleClusterTrace
  have he : (fun ζ : ℂ => Matrix.trace
      (traceDensityPencil H Y z * resolvent (traceDensityPencil H Y z) ζ) /
        (Fintype.card ι : ℂ)) =
      (fun ζ : ℂ => (Fintype.card ι : ℂ)⁻¹ * Matrix.trace
        (traceDensityPencil H Y z * resolvent (traceDensityPencil H Y z) ζ)) := by
    funext ζ
    rw [div_eq_mul_inv, mul_comm]
  rw [he, circleIntegral.integral_const_mul]
  simp only [div_eq_mul_inv]
  ring

end
end CGLMPBounds.Hardy
