module

public import CGLMPBounds.Hardy.PositivePinchingWeightedMoments
public import CGLMPBounds.Hardy.PolynomialTwoNodeBeta

@[expose] public section


/-! The literal substitution x=1−2u in C.13, including every power of two
and factorial. This is the measure side of the C.10 coefficient comparison. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Complex MeasureTheory Set

lemma intervalIntegral_pinching_beta_substitution (g : ℝ → ℂ) (p q : ℕ) :
    (∫ x in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ p * (1 + (x : ℂ)) ^ q * g x) =
      (2 : ℂ) ^ (p + q + 1) *
        ∫ u in (0 : ℝ)..1, (u : ℂ) ^ p * (1 - (u : ℂ)) ^ q * g (1 - 2 * u) := by
  let F : ℝ → ℂ := fun x => (1 - (x : ℂ)) ^ p * (1 + (x : ℂ)) ^ q * g x
  have hs := intervalIntegral.integral_comp_mul_add (f := F) (a := (0 : ℝ)) (b := 1)
    (c := (-2 : ℝ)) (by norm_num) 1
  norm_num only [mul_zero, zero_add, mul_one, neg_add_cancel_right] at hs
  rw [intervalIntegral.integral_symm (-1 : ℝ) (1 : ℝ)] at hs
  have hpoint : (fun u : ℝ => F ((-2) * u + 1)) =
      (fun u : ℝ => (2 : ℂ) ^ (p + q) *
        ((u : ℂ) ^ p * (1 - (u : ℂ)) ^ q * g (1 - 2 * u))) := by
    funext u
    rw [show (-2 : ℝ) * u + 1 = 1 - 2 * u by ring]
    dsimp only [F]
    push_cast
    rw [show (1 : ℂ) - (1 - 2 * (u : ℂ)) = 2 * (u : ℂ) by ring,
      show (1 : ℂ) + (1 - 2 * (u : ℂ)) = 2 * (1 - (u : ℂ)) by ring,
      mul_pow, mul_pow, pow_add]
    ring
  rw [hpoint, intervalIntegral.integral_const_mul, Complex.real_smul] at hs
  norm_num at hs
  change (∫ x in (-1 : ℝ)..1, F x) = _
  rw [pow_succ]
  linear_combination -(2 : ℂ) * hs

lemma choose_div_factorial_eq_reciprocal (m p : ℕ) (hp : p ≤ m) :
    (m.choose p : ℂ) / (m.factorial : ℂ) =
      1 / ((p.factorial : ℂ) * ((m - p).factorial : ℂ)) := by
  have hm0 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hp0 : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hq0 : ((m - p).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m - p)
  apply (div_eq_div_iff hm0 (mul_ne_zero hp0 hq0)).mpr
  simpa only [one_mul, ← mul_assoc, ← Nat.cast_mul] using
    congrArg (fun n : ℕ => (n : ℂ)) (Nat.choose_mul_factorial_mul_factorial hp)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem positivePinching_diagonal_weighted_moment_eq_beta
    (σ : ι → Bool) {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (m : ℕ) {g : ℝ → ℂ} (hg : Continuous g) :
    (∫ p : ℝ × ℝ, g p.1 * (p.2 : ℂ) ^ m
      ∂positivePinchingMeasure (involutionFromSigns σ) Y) / (m.factorial : ℂ) =
      (1 / ((Fintype.card ι : ℂ) * (m + 2))) *
        ∑ v : Fin (m + 2) → ι,
          if 1 ≤ cyclePositiveCount σ v ∧ cyclePositiveCount σ v < m + 2 then
            (1 / (((cyclePositiveCount σ v - 1).factorial : ℂ) *
              ((m + 2 - cyclePositiveCount σ v - 1).factorial : ℂ))) *
              (∫ u in (0 : ℝ)..1, (u : ℂ) ^ (cyclePositiveCount σ v - 1) *
                (1 - (u : ℂ)) ^ (m + 2 - cyclePositiveCount σ v - 1) * g (1 - 2 * u)) *
                  matrixIndexCycleWeight Y (m + 1) v
          else 0 := by
  classical
  let P := fun v : Fin (m + 2) → ι => cyclePositiveCount σ v
  let W := fun v : Fin (m + 2) → ι => matrixIndexCycleWeight Y (m + 1) v
  let F := fun (v : Fin (m + 2) → ι) (x : ℝ) =>
    if 1 ≤ P v ∧ P v < m + 2 then
      (m.choose (P v - 1) : ℂ) * W v *
        ((1 - (x : ℂ)) ^ (P v - 1) * (1 + (x : ℂ)) ^ (m + 2 - P v - 1) * g x)
    else 0
  have hF : ∀ v ∈ (Finset.univ : Finset (Fin (m + 2) → ι)),
      IntervalIntegrable (F v) volume (-1) 1 := by
    intro v _
    by_cases hp : 1 ≤ P v ∧ P v < m + 2
    · simp only [F, if_pos hp]
      apply Continuous.intervalIntegrable
      fun_prop
    · simp only [F, if_neg hp]
      exact intervalIntegrable_const
  have hfun : (fun x : ℝ => g x * pinchingCycleMoment σ Y m x) =
      (fun x : ℝ => (1 / ((Fintype.card ι : ℂ) * (m + 2) * 2 ^ (m + 1))) *
        ∑ v : Fin (m + 2) → ι, F v x) := by
    funext x
    unfold pinchingCycleMoment
    push_cast
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    change g x * (if 1 ≤ P v ∧ P v < m + 2 then _ else _) = F v x
    by_cases hp : 1 ≤ P v ∧ P v < m + 2
    · simp only [F, if_pos hp]
      ring
    · simp only [F, if_neg hp]
      ring
  rw [positivePinching_diagonal_weighted_moment σ hY m hg, hfun,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hF,
    Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  change ((1 / ((Fintype.card ι : ℂ) * (m + 2) * 2 ^ (m + 1))) *
      (∫ x in (-1 : ℝ)..1, F v x)) / (m.factorial : ℂ) =
    (1 / ((Fintype.card ι : ℂ) * (m + 2))) *
      (if 1 ≤ P v ∧ P v < m + 2 then _ else _)
  by_cases hp : 1 ≤ P v ∧ P v < m + 2
  · have hpq : P v - 1 + (m + 2 - P v - 1) + 1 = m + 1 := by omega
    have hmq : m - (P v - 1) = m + 2 - P v - 1 := by omega
    have hcoef := choose_div_factorial_eq_reciprocal m (P v - 1) (by omega)
    rw [hmq] at hcoef
    simp only [F, if_pos hp]
    rw [intervalIntegral.integral_const_mul, intervalIntegral_pinching_beta_substitution, hpq]
    have htwo : (2 : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    calc
      _ = (1 / ((Fintype.card ι : ℂ) * (m + 2))) *
          ((m.choose (P v - 1) : ℂ) / (m.factorial : ℂ)) *
          (∫ u in (0 : ℝ)..1, (u : ℂ) ^ (P v - 1) *
            (1 - (u : ℂ)) ^ (m + 2 - P v - 1) * g (1 - 2 * u)) * W v := by
        field_simp [htwo]
        <;> ring
      _ = _ := by rw [hcoef]; ring
  · simp only [F, if_neg hp, intervalIntegral.integral_zero, mul_zero, zero_div]

end
end CGLMPBounds.Hardy
