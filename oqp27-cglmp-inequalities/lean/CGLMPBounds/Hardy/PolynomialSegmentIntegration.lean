module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section


/-! Actual polynomial integration by parts along a complex segment. These
identities provide the beta recurrences for the two-node contour comparison
in C.10, including endpoint terms when either beta exponent is zero. -/

namespace CGLMPBounds.Hardy
noncomputable section
open MeasureTheory Complex

lemma hasDerivAt_polynomial_segment_weight (f : Polynomial ℂ) (a b : ℂ) (p q : ℕ) (u : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ p * (1 - (t : ℂ)) ^ q *
      f.eval ((t : ℂ) * a + (1 - (t : ℂ)) * b))
      ((p : ℂ) * ((u : ℂ) ^ (p - 1) * (1 - (u : ℂ)) ^ q *
          f.eval ((u : ℂ) * a + (1 - (u : ℂ)) * b)) -
        (q : ℂ) * ((u : ℂ) ^ p * (1 - (u : ℂ)) ^ (q - 1) *
          f.eval ((u : ℂ) * a + (1 - (u : ℂ)) * b)) +
        (a - b) * ((u : ℂ) ^ p * (1 - (u : ℂ)) ^ q *
          f.derivative.eval ((u : ℂ) * a + (1 - (u : ℂ)) * b))) u := by
  have hsegment : HasDerivAt (fun z : ℂ => z * a + (1 - z) * b)
      (a - b) (u : ℂ) := by
    convert ((hasDerivAt_id (u : ℂ)).mul_const a).add
      (((hasDerivAt_id (u : ℂ)).const_sub 1).mul_const b) using 1 <;>
      first | rfl | ring
  have heval := (f.hasDerivAt ((u : ℂ) * a + (1 - (u : ℂ)) * b)).comp (u : ℂ) hsegment
  have hweight := (hasDerivAt_pow p (u : ℂ)).mul
    (((hasDerivAt_id (u : ℂ)).const_sub 1).pow q)
  have h := (hweight.mul heval).comp_ofReal
  convert h using 1 <;> first
    | rfl
    | (dsimp only [Function.comp_def, Pi.mul_apply, Pi.pow_apply, id_eq]; ring)

theorem polynomial_segment_beta_integrationByParts (f : Polynomial ℂ) (a b : ℂ) (p q : ℕ) :
    (a - b) * (∫ u in (0 : ℝ)..1, (u : ℂ) ^ p * (1 - (u : ℂ)) ^ q *
      f.derivative.eval ((u : ℂ) * a + (1 - (u : ℂ)) * b)) =
    (0 : ℂ) ^ q * f.eval a - (0 : ℂ) ^ p * f.eval b -
      (p : ℂ) * (∫ u in (0 : ℝ)..1, (u : ℂ) ^ (p - 1) * (1 - (u : ℂ)) ^ q *
        f.eval ((u : ℂ) * a + (1 - (u : ℂ)) * b)) +
      (q : ℂ) * (∫ u in (0 : ℝ)..1, (u : ℂ) ^ p * (1 - (u : ℂ)) ^ (q - 1) *
        f.eval ((u : ℂ) * a + (1 - (u : ℂ)) * b)) := by
  let P : ℝ → ℂ := fun u => (u : ℂ) ^ (p - 1) * (1 - (u : ℂ)) ^ q *
    f.eval ((u : ℂ) * a + (1 - (u : ℂ)) * b)
  let Q : ℝ → ℂ := fun u => (u : ℂ) ^ p * (1 - (u : ℂ)) ^ (q - 1) *
    f.eval ((u : ℂ) * a + (1 - (u : ℂ)) * b)
  let T : ℝ → ℂ := fun u => (u : ℂ) ^ p * (1 - (u : ℂ)) ^ q *
    f.derivative.eval ((u : ℂ) * a + (1 - (u : ℂ)) * b)
  have hsegment : Continuous (fun u : ℝ => (u : ℂ) * a + (1 - (u : ℂ)) * b) := by
    fun_prop
  have hf := f.differentiable.continuous.comp hsegment
  have hdf := f.derivative.differentiable.continuous.comp hsegment
  have hP : IntervalIntegrable (fun u => (p : ℂ) * P u) volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [P]
    exact continuous_const.mul (((Complex.continuous_ofReal.pow (p - 1)).mul
      ((continuous_const.sub Complex.continuous_ofReal).pow q)).mul hf)
  have hQ : IntervalIntegrable (fun u => (q : ℂ) * Q u) volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [Q]
    exact continuous_const.mul (((Complex.continuous_ofReal.pow p).mul
      ((continuous_const.sub Complex.continuous_ofReal).pow (q - 1))).mul hf)
  have hT : IntervalIntegrable (fun u => (a - b) * T u) volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [T]
    exact continuous_const.mul (((Complex.continuous_ofReal.pow p).mul
      ((continuous_const.sub Complex.continuous_ofReal).pow q)).mul hdf)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_polynomial_segment_weight f a b p q u) ((hP.sub hQ).add hT)
  change (∫ u in (0 : ℝ)..1, (p : ℂ) * P u - (q : ℂ) * Q u + (a - b) * T u) = _ at hFTC
  rw [intervalIntegral.integral_add (hP.sub hQ) hT,
    intervalIntegral.integral_sub hP hQ, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_pow, sub_self,
    zero_mul, one_mul, sub_zero, zero_add, add_zero] at hFTC
  change (a - b) * (∫ u in (0 : ℝ)..1, T u) =
    (0 : ℂ) ^ q * f.eval a - (0 : ℂ) ^ p * f.eval b -
      (p : ℂ) * (∫ u in (0 : ℝ)..1, P u) + (q : ℂ) * (∫ u in (0 : ℝ)..1, Q u)
  linear_combination hFTC

lemma polynomial_segment_fundamental (f : Polynomial ℂ) (a b : ℂ) :
    (a - b) * (∫ u in (0 : ℝ)..1,
      f.derivative.eval ((u : ℂ) * a + (1 - (u : ℂ)) * b)) = f.eval a - f.eval b := by
  simpa using polynomial_segment_beta_integrationByParts f a b 0 0

end
end CGLMPBounds.Hardy
