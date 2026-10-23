module

public import CGLMPBounds.Hardy.PolynomialContourBetaEndpoints
public import CGLMPBounds.Hardy.PolynomialDiagonalResolvent

@[expose] public section


/-! The actual mixed matrix resolvent integral is a finite sum of actual beta
integrals. Both the matrix cycle subtraction and the scalar contour transport
are proved dependencies, so neither is supplied as a premise here. -/

open scoped Polynomial

namespace CGLMPBounds.Hardy
noncomputable section
open Complex Matrix Metric Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma polynomial_two_node_continuousOn_enclosing_circle (f : ℂ[X]) (p q : ℕ)
    {a b c : ℂ} {R : ℝ} (ha : a ∈ ball c R) (hb : b ∈ ball c R) :
    ContinuousOn (fun z : ℂ => f.eval z / ((z - a) ^ p * (z - b) ^ q))
      (sphere c R) := by
  apply f.continuous.continuousOn.div
    (((continuousOn_id.sub continuousOn_const).pow p).mul
      ((continuousOn_id.sub continuousOn_const).pow q))
  intro z hz
  have hza : z ≠ a := by
    intro h
    exact (ne_of_lt (Metric.mem_ball.mp ha)) (Metric.mem_sphere.mp (h ▸ hz))
  have hzb : z ≠ b := by
    intro h
    exact (ne_of_lt (Metric.mem_ball.mp hb)) (Metric.mem_sphere.mp (h ▸ hz))
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hza))
    (pow_ne_zero _ (sub_ne_zero.mpr hzb))

theorem diagonal_two_node_mixed_circleIntegral_eq_beta
    (σ : ι → Bool) (Y : Matrix ι ι ℂ) (m M : ℕ) {a b c : ℂ}
    (hab : a ≠ b) {R : ℝ} (hR : 0 ≤ R)
    (ha : a ∈ ball c R) (hb : b ∈ ball c R) :
    let H := Matrix.diagonal (fun i => if σ i then a else b)
    (∮ z in C(c, R), z ^ M *
      (Matrix.trace ((resolvent H z * Y) ^ (m + 2)) -
        Matrix.trace ((resolvent H z * positivePinchingPart (involutionFromSigns σ) Y) ^
          (m + 2)))) / (2 * Real.pi * Complex.I : ℂ) =
      ∑ v : Fin (m + 2) → ι,
        if 1 ≤ cyclePositiveCount σ v ∧ cyclePositiveCount σ v < m + 2 then
          polynomialBetaDividedDifference (Polynomial.X ^ M) a b
            (cyclePositiveCount σ v - 1) (m + 2 - cyclePositiveCount σ v - 1) *
              matrixIndexCycleWeight Y (m + 1) v
        else 0 := by
  classical
  dsimp only
  let P := fun v : Fin (m + 2) → ι => cyclePositiveCount σ v
  let W := fun v : Fin (m + 2) → ι => matrixIndexCycleWeight Y (m + 1) v
  let F := fun (v : Fin (m + 2) → ι) (z : ℂ) =>
    if 1 ≤ P v ∧ P v < m + 2 then
      (z ^ M / ((z - a) ^ P v * (z - b) ^ (m + 2 - P v))) * W v
    else 0
  have hF : ∀ v ∈ (Finset.univ : Finset (Fin (m + 2) → ι)), CircleIntegrable (F v) c R := by
    intro v _
    by_cases hp : 1 ≤ P v ∧ P v < m + 2
    · simp only [F, hp, and_self, ite_true]
      apply ContinuousOn.circleIntegrable hR
      have hf := polynomial_two_node_continuousOn_enclosing_circle
        (Polynomial.X ^ M) (P v) (m + 2 - P v) ha hb
      simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
        hf.fun_mul (continuousOn_const (c := W v))
    · simp only [F, hp, ite_false]
      exact continuousOn_const.circleIntegrable hR
  have hexpand : (∮ z in C(c, R), z ^ M *
      (Matrix.trace ((resolvent (Matrix.diagonal (fun i => if σ i then a else b)) z * Y) ^
        (m + 2)) - Matrix.trace ((resolvent
          (Matrix.diagonal (fun i => if σ i then a else b)) z *
            positivePinchingPart (involutionFromSigns σ) Y) ^ (m + 2)))) =
        ∑ v : Fin (m + 2) → ι, ∮ z in C(c, R), F v z := by
    rw [← circleIntegral.integral_fun_sum hF]
    apply circleIntegral.integral_congr hR
    intro z hz
    have hza : z ≠ a := by
      intro h
      exact (ne_of_lt (Metric.mem_ball.mp ha)) (Metric.mem_sphere.mp (h ▸ hz))
    have hzb : z ≠ b := by
      intro h
      exact (ne_of_lt (Metric.mem_ball.mp hb)) (Metric.mem_sphere.mp (h ▸ hz))
    exact diagonal_two_node_mixed_resolvent_trace σ Y (m + 1) M a b hza hzb
  rw [hexpand, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hp : 1 ≤ P v ∧ P v < m + 2
  · have hp' : P v - 1 + 1 = P v := by omega
    have hq' : m + 2 - P v - 1 + 1 = m + 2 - P v := by omega
    change (∮ z in C(c, R), F v z) / _ =
      if 1 ≤ P v ∧ P v < m + 2 then _ else _
    simp only [F, hp, and_self, ite_true]
    rw [show (∮ z in C(c, R),
        (z ^ M / ((z - a) ^ P v * (z - b) ^ (m + 2 - P v))) * W v) =
        (∮ z in C(c, R), z ^ M / ((z - a) ^ P v * (z - b) ^ (m + 2 - P v))) * W v by
      simpa only [smul_eq_mul] using circleIntegral.integral_smul_const
        (fun z : ℂ => z ^ M / ((z - a) ^ P v * (z - b) ^ (m + 2 - P v))) (W v) c R]
    have hbeta := polynomial_circleIntegral_eq_beta (Polynomial.X ^ M) hab
      (P v - 1) (m + 2 - P v - 1) hR ha hb
    simp only [Polynomial.eval_pow, Polynomial.eval_X, hp', hq'] at hbeta
    rw [show ((∮ z in C(c, R), z ^ M / ((z - a) ^ P v *
        (z - b) ^ (m + 2 - P v))) * W v) / (2 * Real.pi * Complex.I : ℂ) =
        ((∮ z in C(c, R), z ^ M / ((z - a) ^ P v *
          (z - b) ^ (m + 2 - P v))) / (2 * Real.pi * Complex.I : ℂ)) * W v by ring,
      hbeta]
  · change (∮ z in C(c, R), F v z) / _ =
      if 1 ≤ P v ∧ P v < m + 2 then _ else _
    simp [F, hp, circleIntegral]

end
end CGLMPBounds.Hardy
