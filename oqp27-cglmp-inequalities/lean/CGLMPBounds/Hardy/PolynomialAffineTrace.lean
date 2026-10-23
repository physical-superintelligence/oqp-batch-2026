module

public import CGLMPBounds.Hardy.PolynomialPinchingCoefficient
public import Mathlib.Algebra.Polynomial.Taylor

@[expose] public section


/-! Explicit scalar polynomials for actual matrix power traces. Their
coefficients are identified with literal derivatives, and the constant and
linear coefficients of the actual pinched difference are proved to vanish. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Polynomial
open scoped Matrix.Norms.Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def affineMatrixPolynomial (H Y : Matrix ι ι ℂ) : Matrix ι ι ℂ[X] :=
  fun i j => C (H i j) + X * C (Y i j)

def affinePowerTracePolynomial (H Y : Matrix ι ι ℂ) (N : ℕ) : ℂ[X] :=
  C ((Fintype.card ι : ℂ)⁻¹) * Matrix.trace ((affineMatrixPolynomial H Y) ^ N)

lemma eval_affineMatrixPolynomial (H Y : Matrix ι ι ℂ) (t : ℂ) :
    (Polynomial.evalRingHom t).mapMatrix (affineMatrixPolynomial H Y) = H + t • Y := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, affineMatrixPolynomial,
    Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

lemma eval_affinePowerTracePolynomial (H Y : Matrix ι ι ℂ) (N : ℕ) (t : ℂ) :
    (affinePowerTracePolynomial H Y N).eval t =
      Matrix.trace ((H + t • Y) ^ N) / (Fintype.card ι : ℂ) := by
  unfold affinePowerTracePolynomial
  rw [Polynomial.eval_mul, Polynomial.eval_C, ← Polynomial.coe_evalRingHom,
    AddMonoidHom.map_trace]
  change (Fintype.card ι : ℂ)⁻¹ *
    Matrix.trace ((Polynomial.evalRingHom t).mapMatrix ((affineMatrixPolynomial H Y) ^ N)) = _
  rw [map_pow, eval_affineMatrixPolynomial]
  ring

lemma polynomial_coeff_eq_iteratedDeriv_eval (p : ℂ[X]) (k : ℕ) :
    p.coeff k = iteratedDeriv k (fun z : ℂ => p.eval z) 0 / (k.factorial : ℂ) := by
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [iteratedDeriv_polynomial_eval, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative, Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  exact (mul_div_cancel_left₀ _ hfac).symm

lemma affinePowerTracePolynomial_coeff (H Y : Matrix ι ι ℂ) (N k : ℕ) :
    (affinePowerTracePolynomial H Y N).coeff k =
      iteratedDeriv k (fun t : ℂ => Matrix.trace ((H + t • Y) ^ N)) 0 /
        ((k.factorial : ℂ) * (Fintype.card ι : ℂ)) := by
  rw [polynomial_coeff_eq_iteratedDeriv_eval]
  simp_rw [eval_affinePowerTracePolynomial]
  rw [iteratedDeriv_div_const]
  simp only [div_mul_eq_div_div]
  ring

lemma affinePowerTracePolynomial_coeff_zero (H Y : Matrix ι ι ℂ) (N : ℕ) :
    (affinePowerTracePolynomial H Y N).coeff 0 =
      Matrix.trace (H ^ N) / (Fintype.card ι : ℂ) := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_affinePowerTracePolynomial]
  simp only [zero_smul, add_zero]

lemma affinePowerTracePolynomial_coeff_one (H Y : Matrix ι ι ℂ) (N : ℕ) :
    (affinePowerTracePolynomial H Y N).coeff 1 =
      (N : ℂ) * Matrix.trace (H ^ (N - 1) * Y) / (Fintype.card ι : ℂ) := by
  have harg : HasDerivAt (fun t : ℂ => H + t • Y) Y 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, zero_add] using
      (hasDerivAt_const (0 : ℂ) (H i j)).fun_add
        (hasDerivAt_mul_const (Y i j))
  have hd := hasDerivAt_trace_matrix_pow harg N
  simp only [zero_smul, add_zero] at hd
  rw [affinePowerTracePolynomial_coeff, iteratedDeriv_one, hd.deriv]
  simp only [Nat.factorial_one, Nat.cast_one, one_mul]

lemma trace_diagonal_mul_pinching (σ : ι → Bool) (d : ι → ℂ) (Y : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.diagonal d * positivePinchingPart (involutionFromSigns σ) Y) =
      Matrix.trace (Matrix.diagonal d * Y) := by
  simp only [Matrix.diagonal_mul, Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro i _
  rw [positivePinching_part_signs_apply, if_pos rfl]

theorem pinched_affinePowerTracePolynomial_low_coefficients
    (σ : ι → Bool) (Y : Matrix ι ι ℂ) (s : ℂ) (N : ℕ) :
    let H := s • involutionFromSigns σ
    let C := positivePinchingPart (involutionFromSigns σ) Y
    (affinePowerTracePolynomial H Y N - affinePowerTracePolynomial H C N).coeff 0 = 0 ∧
      (affinePowerTracePolynomial H Y N - affinePowerTracePolynomial H C N).coeff 1 = 0 := by
  dsimp only
  constructor
  · rw [Polynomial.coeff_sub, affinePowerTracePolynomial_coeff_zero,
      affinePowerTracePolynomial_coeff_zero, sub_self]
  · rw [Polynomial.coeff_sub, affinePowerTracePolynomial_coeff_one,
      affinePowerTracePolynomial_coeff_one]
    have hdiag : s • involutionFromSigns σ =
        Matrix.diagonal (fun i => s * (if σ i then (1 : ℂ) else -1)) := by
      ext i j
      by_cases hij : i = j <;> simp [involutionFromSigns, Matrix.diagonal_apply,
        Matrix.smul_apply, hij]
    rw [hdiag, Matrix.diagonal_pow, trace_diagonal_mul_pinching, sub_self]

end
end CGLMPBounds.Hardy
