module

public import CGLMPBounds.Partition.PotentialIdentity

@[expose] public section


/-! Absolute convergence of the literal coefficient integrals in D.9.
The compact fourth derivative is taken within [0,1]; its equality with the
ordinary derivative is used only in the open interval. Thus no two-sided
smoothness assertion at the guarded endpoints is smuggled into the estimate. -/

namespace CGLMPBounds.Partition
open MeasureTheory Set
noncomputable section

lemma partitionPotential_iteratedDerivWithin_eq {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    iteratedDerivWithin m partitionPotential (Icc (0 : ℝ) 1) x =
      iteratedDeriv m partitionPotential x := by
  apply iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
  · exact (partitionPotential_contDiffOn.contDiffAt (Icc_mem_nhds hx.1 hx.2)).of_le
      (by simp)
  · exact ⟨hx.1.le, hx.2.le⟩

lemma partitionFourierCoefficient_eq_within (n : ℕ) :
    partitionFourierCoefficient n =
      (1 / (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2)) *
        ∫ x in (0 : ℝ)..1,
          iteratedDerivWithin 4 partitionPotential (Icc (0 : ℝ) 1) x *
            (1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x)) := by
  unfold partitionFourierCoefficient
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
  intro x hx
  dsimp only
  rw [partitionPotential_iteratedDerivWithin_eq hx]

/-- A summable inverse-square bound on the source's actual coefficients.
No sign or Fourier reconstruction identity is assumed. -/
theorem partitionFourierCoefficient_norm_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖partitionFourierCoefficient n‖ ≤ C * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hc : ContinuousOn
      (iteratedDerivWithin 4 partitionPotential (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) :=
    partitionPotential_contDiffOn.continuousOn_iteratedDerivWithin (by simp)
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num))
  refine ⟨(2 * B) / (4 * Real.pi ^ 2), by positivity, fun n => ?_⟩
  have hweight (x : ℝ) :
      ‖1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x)‖ ≤ 2 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Real.neg_one_le_cos
      (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x),
      Real.cos_le_one (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x)]
  have hi : ‖∫ x in (0 : ℝ)..1,
      iteratedDerivWithin 4 partitionPotential (Icc (0 : ℝ) 1) x *
        (1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x))‖ ≤ 2 * B := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := 2 * B)
      (f := fun x => iteratedDerivWithin 4 partitionPotential (Icc (0 : ℝ) 1) x *
        (1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x))) (by
        intro x hx
        have hx' : x ∈ Icc (0 : ℝ) 1 := by
          simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Ioc] at hx
          exact ⟨hx.1.le, hx.2⟩
        rw [norm_mul]
        calc
          _ ≤ B * 2 := mul_le_mul (hB x hx') (hweight x) (norm_nonneg _) hB0
          _ = 2 * B := by ring)
    simpa using h
  have hfactor : 0 ≤ 1 / (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    positivity
  rw [partitionFourierCoefficient_eq_within, norm_mul,
    Real.norm_eq_abs (1 / _), abs_of_nonneg hfactor]
  calc
    _ ≤ (1 / (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2)) * (2 * B) :=
      mul_le_mul_of_nonneg_left hi hfactor
    _ = (2 * B / (4 * Real.pi ^ 2)) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by ring

/-- Absolute summability for precisely the integral coefficients defined in D.9. -/
theorem partitionFourierCoefficient_summable : Summable partitionFourierCoefficient := by
  obtain ⟨C, _, hC⟩ := partitionFourierCoefficient_norm_bound
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 hp
  exact (hs.mul_left C).of_norm_bounded hC

end
end CGLMPBounds.Partition
