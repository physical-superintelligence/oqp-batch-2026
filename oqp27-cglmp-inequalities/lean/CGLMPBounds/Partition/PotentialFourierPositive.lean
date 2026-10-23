module

public import CGLMPBounds.Partition.PotentialFourth

@[expose] public section


/-! Positivity of each literal D.9 Fourier coefficient. The kernel factor is
nonnegative everywhere and equals one at the quarter-period interior point.
The fourth derivative is the actual source derivative, transferred to a
continuous compact within-derivative only for the integral argument. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
noncomputable section

theorem partitionFourierCoefficient_pos (n : ℕ) : 0 < partitionFourierCoefficient n := by
  let f : ℝ → ℝ := fun x =>
    iteratedDerivWithin 4 partitionPotential (Icc (0 : ℝ) 1) x *
      (1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x))
  have hfourth : ContinuousOn
      (iteratedDerivWithin 4 partitionPotential (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) :=
    partitionPotential_contDiffOn.continuousOn_iteratedDerivWithin (by simp)
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
  have hc : ContinuousOn f (Icc (0 : ℝ) 1) := hfourth.mul (by fun_prop)
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  let c : ℝ := 1 / (4 * ((n + 1 : ℕ) : ℝ))
  have hn1 : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_iff₀ (by positivity : 0 < 4 * ((n + 1 : ℕ) : ℝ))).mpr
    linarith
  have hangle : 2 * Real.pi * ((n + 1 : ℕ) : ℝ) * c = Real.pi / 2 := by
    dsimp [c]
    field_simp [hn.ne']
    <;> ring
  have hcpos : 0 < f c := by
    dsimp [f]
    rw [hangle, Real.cos_pi_div_two, sub_zero, mul_one]
    exact partitionPotential_fourthWithin_pos ⟨hc0.le, hc1⟩
  have hnonneg : ∀ x ∈ Ioc (0 : ℝ) 1, (0 : ℝ) ≤ f x := by
    intro x hx
    exact mul_nonneg (partitionPotential_fourthWithin_pos ⟨hx.1.le, hx.2⟩).le
      (sub_nonneg.mpr (Real.cos_le_one _))
  have hint : 0 < ∫ x in (0 : ℝ)..1, f x := by
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by norm_num : (0 : ℝ) < 1)
      (f := fun _ => (0 : ℝ)) (g := f) continuousOn_const hc hnonneg
      ⟨c, ⟨hc0.le, hc1⟩, hcpos⟩
    simpa using h
  rw [partitionFourierCoefficient_eq_within]
  exact mul_pos (by positivity) hint

end
end CGLMPBounds.Partition
