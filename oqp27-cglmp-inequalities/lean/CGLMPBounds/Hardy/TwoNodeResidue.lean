module

public import CGLMPBounds.Hardy.TwoNodeDerivatives
public import CGLMPBounds.Defs.TwoNodeResidue

@[expose] public section


/-!
# The actual small-circle residue in source C.9

The residue is defined by the normalized integral of the displayed rational
function on the circle centered at `a` with radius `|a-b|/2`. That closed disk
excludes `b`. Cauchy's derivative formula and the separate exact derivative
calculation give the printed binomial value for `p,q >= 1` and `a > 0 > b`.
The residue is not defined by the claimed answer, and no change-of-coordinate
or residue oracle is used.

Canonical source: supplement printed page 9, equation C.9.
-/

open Complex Metric Set
open scoped Real

namespace CGLMPBounds.Hardy
noncomputable section

lemma twoNode_radius_pos {a b : ℝ} (hab : a ≠ b) : 0 < |a - b| / 2 :=
  div_pos (abs_pos.mpr (sub_ne_zero.mpr hab)) (by norm_num)

lemma twoNode_closedBall_ne_right {a b : ℝ} (hab : a ≠ b) {z : ℂ}
    (hz : z ∈ closedBall (a : ℂ) (|a - b| / 2)) : z ≠ (b : ℂ) := by
  intro heq
  subst z
  have hdist : dist (b : ℂ) (a : ℂ) = |a - b| := by
    simpa only [Real.dist_eq, abs_sub_comm] using Complex.isometry_ofReal.dist_eq b a
  have hb := Metric.mem_closedBall.mp hz
  rw [hdist] at hb
  have hpos := abs_pos.mpr (sub_ne_zero.mpr hab)
  linarith

/-- Cauchy's formula expresses this particular contour integral as the
actual derivative of its regular factor, divided by the factorial. -/
theorem twoNodeResidue_eq_iteratedDeriv (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    {a b : ℝ} (hab : a ≠ b) :
    twoNodeResidue p q a b =
      iteratedDeriv (p - 1) (twoNodeRegularFactor (p - 1) q (b : ℂ)) (a : ℂ) /
        ((p - 1).factorial : ℂ) := by
  have hc : DifferentiableOn ℂ (twoNodeRegularFactor (p - 1) q (b : ℂ))
      (closedBall (a : ℂ) (|a - b| / 2)) := by
    intro z hz
    exact (analyticAt_twoNodeRegularFactor (p - 1) q (b : ℂ)
      (twoNode_closedBall_ne_right hab hz)).differentiableAt.differentiableWithinAt
  have hC := DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul
    (twoNode_radius_pos hab) (p - 1) hc
  have hfun : (fun z : ℂ => (1 / (z - (a : ℂ)) ^ (p - 1 + 1)) •
      twoNodeRegularFactor (p - 1) q (b : ℂ) z) =
      (fun z : ℂ => z ^ (p + q - 2) /
        ((z - (a : ℂ)) ^ p * (z - (b : ℂ)) ^ q)) := by
    funext z
    simp only [twoNodeRegularFactor, smul_eq_mul,
      show p - 1 + 1 = p by omega,
      show p - 1 + q - 1 = p + q - 2 by omega,
      div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hfun, smul_eq_mul] at hC
  unfold twoNodeResidue
  rw [hC]
  have hfac : ((p - 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (p - 1)
  field_simp [Complex.two_pi_I_ne_zero, hfac]
  <;> ring

/-- The exact two-node residue printed in C.9. All powers and signs use the
source convention: the positive node is `a`, the negative node is `b`. -/
theorem twoNodeResidue_eq_source (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    {a b : ℝ} (ha : 0 < a) (hb : b < 0) :
    twoNodeResidue p q a b =
      ((p + q - 2).choose (p - 1) : ℂ) * (a : ℂ) ^ (q - 1) *
        (-(b : ℂ)) ^ (p - 1) / ((a : ℂ) - (b : ℂ)) ^ (p + q - 1) := by
  have hab : a ≠ b := by linarith
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have habC : (a : ℂ) ≠ (b : ℂ) := by exact_mod_cast hab
  rw [twoNodeResidue_eq_iteratedDeriv p q hp hq hab,
    iteratedDeriv_twoNodeRegularFactor (p - 1) q hq (b : ℂ) ha0 habC,
    twoNodeDerivativeValue, Nat.ascFactorial_eq_factorial_mul_choose', Nat.cast_mul,
    show q + (p - 1) - 1 = p + q - 2 by omega,
    show q + (p - 1) = p + q - 1 by omega]
  have hfac : ((p - 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (p - 1)
  field_simp [hfac, sub_ne_zero.mpr habC]
  <;> ring

/-- Same source formula with the printed total degree `m=p+q` explicit. -/
theorem twoNodeResidue_eq_source_total (m p q : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : p + q = m)
    {a b : ℝ} (ha : 0 < a) (hb : b < 0) :
    twoNodeResidue p q a b =
      ((m - 2).choose (p - 1) : ℂ) * (a : ℂ) ^ (q - 1) *
        (-(b : ℂ)) ^ (p - 1) / ((a : ℂ) - (b : ℂ)) ^ (m - 1) := by
  simpa only [hm] using twoNodeResidue_eq_source p q hp hq ha hb

end
end CGLMPBounds.Hardy
