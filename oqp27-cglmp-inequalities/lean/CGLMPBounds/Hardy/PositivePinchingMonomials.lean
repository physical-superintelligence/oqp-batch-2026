module

public import CGLMPBounds.Hardy.PolynomialIntegratedTaylor

@[expose] public section


/-! Reconstruction of the actual C.10 monomial identity. Equality of all
literal Taylor coefficients gives equality of explicit finite polynomials.
A second polynomial identity principle extends the initial nonzero real-s
calculation to every complex s, including zero. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Complex Matrix Polynomial MeasureTheory Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem positivePinching_diagonal_monomial_polynomial
    (σ : ι → Bool) {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : s ≠ 0) :
    let B := involutionFromSigns σ
    let C := positivePinchingPart B Y
    affinePowerTracePolynomial ((s : ℂ) • B) Y N -
      affinePowerTracePolynomial ((s : ℂ) • B) C N =
        pinchingIntegralPolynomial B Y (X ^ N) (s : ℂ) := by
  dsimp only
  ext k
  rcases k with _ | k
  · rw [(pinched_affinePowerTracePolynomial_low_coefficients σ Y (s : ℂ) N).1,
      (pinchingIntegralPolynomial_low_coefficients (involutionFromSigns σ) Y (X ^ N) (s : ℂ)).1]
  · rcases k with _ | m
    · rw [(pinched_affinePowerTracePolynomial_low_coefficients σ Y (s : ℂ) N).2,
        (pinchingIntegralPolynomial_low_coefficients (involutionFromSigns σ) Y (X ^ N) (s : ℂ)).2]
    · change (affinePowerTracePolynomial ((s : ℂ) • involutionFromSigns σ) Y N -
        affinePowerTracePolynomial ((s : ℂ) • involutionFromSigns σ)
          (positivePinchingPart (involutionFromSigns σ) Y) N).coeff (m + 2) =
        (pinchingIntegralPolynomial (involutionFromSigns σ) Y (X ^ N) (s : ℂ)).coeff (m + 2)
      rw [Polynomial.coeff_sub, affinePowerTracePolynomial_coeff,
        affinePowerTracePolynomial_coeff, pinchingIntegralPolynomial_coeff]
      exact positivePinching_diagonal_monomial_coefficient σ hY m hN hs

theorem positivePinching_diagonal_monomial_real
    (σ : ι → Bool) {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (N : ℕ) {s : ℝ} (hs : s ≠ 0) (t : ℂ) :
    let B := involutionFromSigns σ
    let C := positivePinchingPart B Y
    Matrix.trace (((s : ℂ) • B + t • Y) ^ N) / (Fintype.card ι : ℂ) -
      Matrix.trace (((s : ℂ) • B + t • C) ^ N) / (Fintype.card ι : ℂ) =
      t ^ 2 * ∫ p : ℝ × ℝ, (X ^ N : ℂ[X]).derivative.derivative.eval
        (-(s : ℂ) * p.1 + t * p.2) ∂positivePinchingMeasure B Y := by
  by_cases hN : N = 0
  · subst N
    simp only [pow_zero, sub_self, Polynomial.derivative_one, Polynomial.derivative_zero,
      Polynomial.eval_zero, integral_zero, mul_zero]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have he := congrArg (fun f : ℂ[X] => f.eval t)
      (positivePinching_diagonal_monomial_polynomial σ hY hNpos hs)
    simpa only [Polynomial.eval_sub, eval_affinePowerTracePolynomial,
      eval_pinchingIntegralPolynomial (involutionFromSigns_isHermitian σ)
        (involutionFromSigns_sq σ) hY] using he

theorem positivePinching_diagonal_monomial
    (σ : ι → Bool) {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (N : ℕ) (s t : ℂ) :
    let B := involutionFromSigns σ
    let C := positivePinchingPart B Y
    Matrix.trace ((s • B + t • Y) ^ N) / (Fintype.card ι : ℂ) -
      Matrix.trace ((s • B + t • C) ^ N) / (Fintype.card ι : ℂ) =
      t ^ 2 * ∫ p : ℝ × ℝ, (X ^ N : ℂ[X]).derivative.derivative.eval
        (-s * p.1 + t * p.2) ∂positivePinchingMeasure B Y := by
  let B := involutionFromSigns σ
  let C := positivePinchingPart B Y
  let P : ℂ[X] := affinePowerTracePolynomial (t • Y) B N -
    affinePowerTracePolynomial (t • C) B N
  let Q : ℂ[X] := Polynomial.C (t ^ 2) *
    integratedAffinePolynomial (positivePinchingMeasure B Y)
      (X ^ N : ℂ[X]).derivative.derivative
        (fun p : ℝ × ℝ => t * p.2) (fun p => -(p.1 : ℂ))
  have hP (z : ℂ) : P.eval z =
      Matrix.trace ((z • B + t • Y) ^ N) / (Fintype.card ι : ℂ) -
        Matrix.trace ((z • B + t • C) ^ N) / (Fintype.card ι : ℂ) := by
    simp only [P, Polynomial.eval_sub, eval_affinePowerTracePolynomial,
      add_comm (t • Y), add_comm (t • C)]
  have hQ (z : ℂ) : Q.eval z =
      t ^ 2 * ∫ p : ℝ × ℝ, (X ^ N : ℂ[X]).derivative.derivative.eval
        (-z * p.1 + t * p.2) ∂positivePinchingMeasure B Y := by
    dsimp only [Q]
    rw [Polynomial.eval_mul, Polynomial.eval_C,
      eval_integratedAffinePolynomial _ _ _ _
        (positivePinching_integratedAffine_integrable (involutionFromSigns_isHermitian σ)
          (involutionFromSigns_sq σ) hY (X ^ N : ℂ[X]).derivative.derivative
            (by fun_prop) (by fun_prop))]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with p
    congr 1
    ring
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinj : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℂ)) := by
      intro n m h
      change ((n + 1 : ℕ) : ℂ) = ((m + 1 : ℕ) : ℂ) at h
      have hn : n + 1 = m + 1 := by exact_mod_cast h
      omega
    apply (Set.infinite_range_of_injective hinj).mono
    rintro z ⟨n, rfl⟩
    change P.eval ((n + 1 : ℕ) : ℂ) = Q.eval ((n + 1 : ℕ) : ℂ)
    rw [hP, hQ]
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    simpa only [Complex.ofReal_natCast] using
      positivePinching_diagonal_monomial_real σ hY N hn t
  dsimp only
  rw [← hP s, ← hQ s, hPQ]

theorem positivePinching_monomial
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) (N : ℕ) (s t : ℂ) :
    Matrix.trace ((s • B + t • Y) ^ N) / (Fintype.card ι : ℂ) -
      Matrix.trace ((s • B + t • positivePinchingPart B Y) ^ N) / (Fintype.card ι : ℂ) =
      t ^ 2 * ∫ p : ℝ × ℝ, (X ^ N : ℂ[X]).derivative.derivative.eval
        (-s * p.1 + t * p.2) ∂positivePinchingMeasure B Y := by
  obtain ⟨U, σ, hBdiag⟩ := hermitian_involution_exists_sign_diagonal hB hB2
  let φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  let Y' : Matrix ι ι ℂ := φ.symm Y
  have hY' : Y'.IsHermitian := (show IsSelfAdjoint Y from hY).map φ.symm
  have hYY : Unitary.conjStarAlgAut ℂ _ U Y' = Y := φ.apply_symm_apply Y
  rw [hBdiag, ← hYY, positivePinching_part_conjStarAlgAut,
    positivePinching_measure_conjStarAlgAut]
  rw [← map_smul, ← map_smul, ← map_add, ← map_pow, trace_conjStarAlgAut,
    ← map_smul, ← map_smul, ← map_add, ← map_pow, trace_conjStarAlgAut]
  simpa only [map_smul] using positivePinching_diagonal_monomial σ hY' N s t

end
end CGLMPBounds.Hardy
