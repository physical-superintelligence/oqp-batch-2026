module

public import CGLMPBounds.Hardy.PolynomialMixedCycleContour
public import CGLMPBounds.Hardy.PolynomialWholeCircleTrace

@[expose] public section


/-! Actual Taylor coefficients of the pinched trace difference at any
Hermitian two-node matrix. This combines whole-spectrum analytic functional
calculus, literal mixed cycles, and the constructed beta contour identity. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Complex Matrix Metric Set
open scoped Matrix.Norms.Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem diagonal_two_node_mixed_trace_taylor_coefficient
    (σ : ι → Bool) {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (m : ℕ) {N : ℕ} (hN : 0 < N) {a b : ℝ} (hab : a ≠ b)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (ha : (a : ℂ) ∈ ball c R) (hb : (b : ℂ) ∈ ball c R) :
    let H := Matrix.diagonal (fun i => if σ i then (a : ℂ) else (b : ℂ))
    let C := positivePinchingPart (involutionFromSigns σ) Y
    iteratedDeriv (m + 2) (fun t : ℂ => Matrix.trace ((H + t • Y) ^ N)) 0 /
        (((m + 2).factorial : ℂ) * (Fintype.card ι : ℂ)) -
      iteratedDeriv (m + 2) (fun t : ℂ => Matrix.trace ((H + t • C) ^ N)) 0 /
        (((m + 2).factorial : ℂ) * (Fintype.card ι : ℂ)) =
      ((N : ℂ) / (m + 2)) / (Fintype.card ι : ℂ) *
        ∑ v : Fin (m + 2) → ι,
          if 1 ≤ cyclePositiveCount σ v ∧ cyclePositiveCount σ v < m + 2 then
            polynomialBetaDividedDifference (Polynomial.X ^ (N - 1)) (a : ℂ) (b : ℂ)
              (cyclePositiveCount σ v - 1) (m + 2 - cyclePositiveCount σ v - 1) *
                matrixIndexCycleWeight Y (m + 1) v
          else 0 := by
  let H : Matrix ι ι ℂ := Matrix.diagonal (fun i => if σ i then (a : ℂ) else (b : ℂ))
  let C := positivePinchingPart (involutionFromSigns σ) Y
  have hH : H.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    cases hi : σ i <;> simp [hi, isSelfAdjoint_iff]
  have hC : C.IsHermitian := positivePinching_part_hermitian (involutionFromSigns_isHermitian σ) hY
  have hin : spectrum ℂ H ⊆ ball c R := by
    intro z hz
    dsimp only [H] at hz
    rw [spectrum_diagonal] at hz
    obtain ⟨i, rfl⟩ := hz
    cases hi : σ i
    · simpa only [hi, Bool.false_eq_true, if_false] using hb
    · simpa only [hi, if_true] using ha
  have hsep : ∀ z ∈ sphere c R, z ∉ spectrum ℂ H := by
    intro z hz hs
    exact (ne_of_lt (Metric.mem_ball.mp (hin hs))) (Metric.mem_sphere.mp hz)
  have hint (Z : Matrix ι ι ℂ) :
      CircleIntegrable (fun z => z ^ (N - 1) *
        Matrix.trace ((resolvent H z * Z) ^ (m + 2))) c R := by
    let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
    have hc := tr.continuous.comp_continuousOn
      (((continuousOn_matrix_resolvent H hsep).mul
        (continuousOn_const (c := Z))).pow (m + 2))
    exact ((continuousOn_id.pow (N - 1)).mul hc).circleIntegrable hR
  have hdiff :
      (∮ z in C(c, R), z ^ (N - 1) * Matrix.trace ((resolvent H z * Y) ^ (m + 2))) -
        (∮ z in C(c, R), z ^ (N - 1) * Matrix.trace ((resolvent H z * C) ^ (m + 2))) =
      ∮ z in C(c, R), z ^ (N - 1) *
        (Matrix.trace ((resolvent H z * Y) ^ (m + 2)) -
          Matrix.trace ((resolvent H z * C) ^ (m + 2))) := by
    rw [← circleIntegral.integral_sub (hint Y) (hint C)]
    apply circleIntegral.integral_congr hR
    intro z _
    ring
  have hac : (a : ℂ) ≠ (b : ℂ) := by exact_mod_cast hab
  have hbeta := diagonal_two_node_mixed_circleIntegral_eq_beta σ Y m (N - 1) hac hR ha hb
  change iteratedDeriv (m + 2) (fun t : ℂ => Matrix.trace ((H + t • Y) ^ N)) 0 / _ -
    iteratedDeriv (m + 2) (fun t : ℂ => Matrix.trace ((H + t • C) ^ N)) 0 / _ = _
  rw [trace_pow_taylor_coefficient_whole_circle hH hY (by omega) hN hR hin,
    trace_pow_taylor_coefficient_whole_circle hH hC (by omega) hN hR hin]
  calc
    _ = ((N : ℂ) / (m + 2)) / (Fintype.card ι : ℂ) *
        (((∮ z in C(c, R), z ^ (N - 1) * Matrix.trace ((resolvent H z * Y) ^ (m + 2))) -
          (∮ z in C(c, R), z ^ (N - 1) * Matrix.trace ((resolvent H z * C) ^ (m + 2)))) /
            (2 * Real.pi * Complex.I : ℂ)) := by push_cast; ring
    _ = _ := by rw [hdiff, hbeta]

end
end CGLMPBounds.Hardy
