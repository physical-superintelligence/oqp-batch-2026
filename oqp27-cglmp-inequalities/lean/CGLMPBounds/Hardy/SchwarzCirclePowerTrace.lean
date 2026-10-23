module

public import CGLMPBounds.Hardy.CircleClusterTrace
public import CGLMPBounds.Defs.PositiveTrace
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

@[expose] public section


/-! Actual fixed-circle functional calculus for powers of selected roots.
Cauchy's formula and the characteristic-root trace-resolvent identity retain
all algebraic multiplicities. For a Hermitian matrix and a circle selecting
its positive roots, this is its actual positive-part power trace. No root
simplicity, cluster identity or diagonalizability premise is introduced. -/

open Complex Metric Set
open scoped Classical Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

lemma powerRootFraction_circleIntegrable (m : ℕ) {c a : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (ha : a ∉ sphere c R) :
    CircleIntegrable (fun ζ : ℂ => ζ ^ m / (ζ - a)) c R := by
  apply ContinuousOn.circleIntegrable hR
  exact (continuousOn_id.pow m).div (continuousOn_id.sub continuousOn_const)
    (fun ζ hζ => sub_ne_zero.mpr (ne_of_mem_of_not_mem hζ ha))

lemma circleIntegral_powerRootFraction (m : ℕ) {c a : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (ha : a ∉ sphere c R) :
    (∮ ζ in C(c, R), ζ ^ m / (ζ - a)) =
      (2 * Real.pi * Complex.I : ℂ) * (if a ∈ ball c R then a ^ m else 0) := by
  classical
  by_cases hin : a ∈ ball c R
  · rw [if_pos hin]
    exact Complex.circleIntegral_div_sub_of_differentiable_on_off_countable
      Set.countable_empty hin (continuousOn_id.pow m)
      (fun ζ _ => differentiableAt_id.pow m)
  · rw [if_neg hin, mul_zero]
    have hout : a ∉ closedBall c R := by
      intro hc
      apply ha
      exact Metric.mem_sphere.mpr (le_antisymm hc (le_of_not_gt hin))
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      hR (s := (∅ : Set ℂ)) Set.countable_empty
    · exact (continuousOn_id.pow m).div (continuousOn_id.sub continuousOn_const)
        (fun ζ hζ => sub_ne_zero.mpr (ne_of_mem_of_not_mem hζ hout))
    · intro ζ hζ
      exact (differentiableAt_id.pow m).div (differentiableAt_id.sub_const a)
        (sub_ne_zero.mpr (ne_of_mem_of_not_mem (ball_subset_closedBall hζ.1) hout))

lemma powerRootFractionSum_circleIntegrable (s : Multiset ℂ) (m : ℕ)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hsep : ∀ a ∈ s, a ∉ sphere c R) :
    CircleIntegrable (fun ζ => (s.map (fun a => ζ ^ m / (ζ - a))).sum) c R := by
  revert hsep
  induction s using Multiset.induction_on with
  | empty => intro _; simpa using circleIntegrable_const (0 : ℂ) c R
  | @cons a s ih =>
    intro hsep
    simp only [Multiset.map_cons, Multiset.sum_cons]
    change CircleIntegrable ((fun ζ : ℂ => ζ ^ m / (ζ - a)) +
      (fun ζ => (s.map (fun b => ζ ^ m / (ζ - b))).sum)) c R
    exact
      (powerRootFraction_circleIntegrable m hR (hsep a (Multiset.mem_cons_self _ _))).add
        (ih (fun b hb => hsep b (Multiset.mem_cons_of_mem hb)))

lemma circleIntegral_powerRootFractionSum (s : Multiset ℂ) (m : ℕ)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hsep : ∀ a ∈ s, a ∉ sphere c R) :
    (∮ ζ in C(c, R), (s.map (fun a => ζ ^ m / (ζ - a))).sum) =
      (2 * Real.pi * Complex.I : ℂ) *
        (s.map (fun a => if a ∈ ball c R then a ^ m else 0)).sum := by
  classical
  revert hsep
  induction s using Multiset.induction_on with
  | empty => intro _; simp [circleIntegral]
  | @cons a s ih =>
    intro hsep
    have ha := hsep a (Multiset.mem_cons_self _ _)
    have hs : ∀ b ∈ s, b ∉ sphere c R := fun b hb => hsep b (Multiset.mem_cons_of_mem hb)
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [circleIntegral.integral_add (powerRootFraction_circleIntegrable m hR ha)
      (powerRootFractionSum_circleIntegrable s m hR hs),
      circleIntegral_powerRootFraction m hR ha, ih hs]
    ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- The normalized integral of ζ^m times the actual trace resolvent. -/
def circlePowerTrace (A : Matrix ι ι ℂ) (m : ℕ) (c : ℂ) (R : ℝ) : ℂ :=
  (∮ ζ in C(c, R), ζ ^ m * Matrix.trace (resolvent A ζ)) /
    (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ)

theorem circlePowerTrace_eq_root_sum (A : Matrix ι ι ℂ) (m : ℕ)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hsep : ∀ a ∈ A.charpoly.roots, a ∉ sphere c R) :
    circlePowerTrace A m c R =
      (A.charpoly.roots.map (fun a => if a ∈ ball c R then a ^ m else 0)).sum /
        (Fintype.card ι : ℂ) := by
  have hint : (∮ ζ in C(c, R), ζ ^ m * Matrix.trace (resolvent A ζ)) =
      ∮ ζ in C(c, R), (A.charpoly.roots.map (fun a => ζ ^ m / (ζ - a))).sum := by
    apply circleIntegral.integral_congr hR
    intro ζ hζ
    dsimp only
    rw [trace_resolvent_eq_root_sum A
      (circle_not_mem_spectrum_of_root_separation A hsep hζ)]
    induction A.charpoly.roots using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, mul_add, ih, mul_one_div]
  unfold circlePowerTrace
  rw [hint, circleIntegral_powerRootFractionSum A.charpoly.roots m hR hsep,
    mul_div_cancel_left₀ _ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])]

/-- The reviewed characteristic-root positive trace agrees with genuine
continuous functional calculus, rather than with a surrogate scalar matrix. -/
theorem positiveTracePower_eq_cfc_trace {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (m : ℕ) :
    (positiveTracePower A m : ℂ) =
      Matrix.trace (cfc (fun x : ℝ => (max x 0) ^ m) A) / (Fintype.card ι : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal]
  unfold positiveTracePower
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp [Multiset.map_map, Function.comp_def, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_sum]

/-- For positive powers, selecting exactly the positive real roots computes
τ((A_+)^m). The exponent restriction excludes the false m=0 identification. -/
theorem circlePowerTrace_eq_positiveTracePower {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) {m : ℕ} (hm : 0 < m) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hsep : ∀ a ∈ A.charpoly.roots, a ∉ sphere c R)
    (hselect : ∀ a ∈ A.charpoly.roots, a ∈ ball c R ↔ 0 < a.re) :
    circlePowerTrace A m c R = (positiveTracePower A m : ℂ) := by
  classical
  rw [circlePowerTrace_eq_root_sum A m hR hsep]
  unfold positiveTracePower
  rw [Complex.ofReal_div]
  push_cast
  apply congrArg (fun t : ℂ => t / (Fintype.card ι : ℂ))
  change _ = Complex.ofRealHom
    (A.charpoly.roots.map (fun z => (max z.re 0) ^ m)).sum
  rw [map_multiset_sum Complex.ofRealHom]
  apply congrArg Multiset.sum
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a ha
  have him : a.im = 0 := by
    rw [hA.roots_charpoly_eq_eigenvalues] at ha
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ha
    simp
  have heq : (a.re : ℂ) = a := by apply Complex.ext <;> simp [him]
  rw [hselect a ha]
  by_cases hp : 0 < a.re
  · simp [hp, max_eq_left hp.le, heq]
  · simp [hp, max_eq_right (le_of_not_gt hp), hm.ne']

end
end CGLMPBounds.Hardy
