module

public import CGLMPBounds.Partition.ScalarQuarterFourier
public import Mathlib.Analysis.Complex.AbelLimit

@[expose] public section


/-! Honest summability and Abel limit of the scalar baseline, with the
single exponential convention used in the finite cell pairing. -/

namespace CGLMPBounds.Partition
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma scalar_quarter_combined_coefficient (n : ℕ) :
    (∫ t in (0 : ℝ)..1,
      Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * t : ℝ) : ℂ)) * Complex.I)) =
      ∫ t in (0 : ℝ)..1,
        Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((-Real.pi * t / 2 : ℝ) : ℂ) * Complex.I) := by
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem scalar_quarter_combined_energy_summable :
    Summable (fun n : ℕ => ‖∫ t in (0 : ℝ)..1,
      Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * t : ℝ) : ℂ)) * Complex.I)‖ ^ 2) := by
  have hi : Function.Injective (fun n : ℕ => 4 * n + 3) := by
    intro m n h
    change 4 * m + 3 = 4 * n + 3 at h
    omega
  have hs := hasSum_zeta_two.summable.comp_injective hi
  have hs' : Summable (fun n : ℕ => (1 : ℝ) / (4 * (n : ℝ) + 3) ^ 2) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hs
  simp_rw [scalar_quarter_combined_coefficient, scalar_quarter_negative_coefficient_norm_sq]
  exact hs'.mul_left (8 / Real.pi ^ 2)

theorem scalar_quarter_combined_abel_limit :
    Tendsto (fun q : ℝ => ∑' n : ℕ,
      ‖∫ t in (0 : ℝ)..1,
        Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * t : ℝ) : ℂ)) * Complex.I)‖ ^ 2 * q ^ n)
      (𝓝[<] (1 : ℝ)) (𝓝 sourceFourthRootHardyConstant) := by
  have hsum : (∑' n : ℕ,
      ‖∫ t in (0 : ℝ)..1,
        Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * t : ℝ) : ℂ)) * Complex.I)‖ ^ 2) =
      sourceFourthRootHardyConstant := by
    simp_rw [scalar_quarter_combined_coefficient]
    exact scalar_quarter_negative_energy
  have h := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    scalar_quarter_combined_energy_summable.hasSum.tendsto_sum_nat
  rwa [hsum] at h

end
end CGLMPBounds.Partition
