module

public import CGLMPBounds.Partition.PotentialPeriodicSecond

@[expose] public section


/-! Identification of all complex Fourier coefficients of the actual
continuous second-derivative circle function. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Topology
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

lemma partitionSecondCircle_fourierCoeff_formula (j : ℤ) :
    fourierCoeff partitionSecondCircle j =
      ((∫ x in (0 : ℝ)..1, partitionPotentialSecond x *
        Real.cos (2 * Real.pi * (j : ℝ) * x)) : ℂ) -
      ((∫ x in (0 : ℝ)..1, partitionPotentialSecond x *
        Real.sin (2 * Real.pi * (j : ℝ) * x)) : ℂ) * Complex.I := by
  let c : ℝ → ℝ := fun x => partitionPotentialSecond x * Real.cos (2 * Real.pi * (j : ℝ) * x)
  let s : ℝ → ℝ := fun x => partitionPotentialSecond x * Real.sin (2 * Real.pi * (j : ℝ) * x)
  have hc : ContinuousOn c (Icc (0 : ℝ) 1) := partitionPotentialSecond_continuousOn.mul (by fun_prop)
  have hs : ContinuousOn s (Icc (0 : ℝ) 1) := partitionPotentialSecond_continuousOn.mul (by fun_prop)
  have hcI : IntervalIntegrable (fun x => (c x : ℂ)) volume 0 1 :=
    (Complex.continuous_ofReal.comp_continuousOn hc).intervalIntegrable_of_Icc (by norm_num)
  have hsI : IntervalIntegrable (fun x => (s x : ℂ)) volume 0 1 :=
    (Complex.continuous_ofReal.comp_continuousOn hs).intervalIntegrable_of_Icc (by norm_num)
  change fourierCoeff (AddCircle.liftIco 1 0 (fun x => (partitionPotentialSecond x : ℂ))) j = _
  rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
  norm_num only [zero_add, sub_zero, one_div_one, one_smul]
  calc
    _ = ∫ x in (0 : ℝ)..1, (c x : ℂ) - (s x : ℂ) * Complex.I := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [fourier_coe_apply]
      simp only [zero_add, sub_zero]
      have he : 2 * (Real.pi : ℂ) * Complex.I * (-j : ℤ) * (x : ℂ) / (1 : ℝ) =
          ((-(2 * Real.pi * (j : ℝ) * x) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [he, Complex.exp_mul_I]
      simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
        smul_eq_mul, c, s]
      push_cast
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub hcI (hsI.mul_const Complex.I),
        intervalIntegral.integral_mul_const]
      simp only [c, s, Complex.ofReal_mul]

lemma partitionSecondCircle_fourierCoeff_zero : fourierCoeff partitionSecondCircle 0 = 0 := by
  rw [partitionSecondCircle_fourierCoeff_formula]
  simp [intervalIntegral.integral_ofReal, integral_partitionPotentialSecond]

lemma partitionSecondCircle_fourierCoeff_pos (n : ℕ) :
    fourierCoeff partitionSecondCircle ((n + 1 : ℕ) : ℤ) = (partitionFourierCoefficient n : ℂ) := by
  rw [partitionSecondCircle_fourierCoeff_formula]
  simp only [Int.cast_natCast, ← Complex.ofReal_mul, intervalIntegral.integral_ofReal,
    partitionPotentialSecond_cosine, partitionPotentialSecond_sine,
    Complex.ofReal_zero, zero_mul, sub_zero]

lemma partitionSecondCircle_fourierCoeff_neg (n : ℕ) :
    fourierCoeff partitionSecondCircle (-((n + 1 : ℕ) : ℤ)) = (partitionFourierCoefficient n : ℂ) := by
  rw [partitionSecondCircle_fourierCoeff_formula]
  simp only [← Complex.ofReal_mul, intervalIntegral.integral_ofReal]
  have hcos : (fun x : ℝ => Real.cos (2 * Real.pi * ((-((n + 1 : ℕ) : ℤ) : ℤ) : ℝ) * x)) =
      (fun x => Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x)) := by
    funext x
    push_cast
    rw [show 2 * Real.pi * -((n : ℝ) + 1) * x = -(2 * Real.pi * ((n : ℝ) + 1) * x) by ring,
      Real.cos_neg]
  have hsin : (fun x : ℝ => Real.sin (2 * Real.pi * ((-((n + 1 : ℕ) : ℤ) : ℤ) : ℝ) * x)) =
      (fun x => -Real.sin (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x)) := by
    funext x
    push_cast
    rw [show 2 * Real.pi * -((n : ℝ) + 1) * x = -(2 * Real.pi * ((n : ℝ) + 1) * x) by ring,
      Real.sin_neg]
  simp_rw [congrFun hcos, congrFun hsin, mul_neg]
  rw [intervalIntegral.integral_neg, partitionPotentialSecond_cosine, partitionPotentialSecond_sine]
  simp

lemma partitionSecondCircle_fourierCoeff_summable : Summable (fourierCoeff partitionSecondCircle) := by
  have ha : Summable (fun n => (partitionFourierCoefficient n : ℂ)) :=
    Complex.summable_ofReal.mpr partitionFourierCoefficient_summable
  apply Summable.of_nat_of_neg_add_one
  · exact (summable_nat_add_iff 1).1
      (ha.congr fun n => (partitionSecondCircle_fourierCoeff_pos n).symm)
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (ha.congr fun n => (partitionSecondCircle_fourierCoeff_neg n).symm)

end
end CGLMPBounds.Partition
