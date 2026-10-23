module

public import CGLMPBounds.Partition.PotentialFourierCoefficients

@[expose] public section


/-! The exact D.9 coefficient mass follows from genuine Fourier inversion
of the actual continuous second derivative at zero. This module invokes
Mathlib's proved summable Fourier reconstruction theorem, not an assumed
source identity. -/

namespace CGLMPBounds.Partition
open scoped Topology
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The exact coefficient mass printed after D.9. -/
theorem partitionFourierCoefficient_tsum :
    (∑' n, partitionFourierCoefficient n) = Real.pi / 4 - 1 / 2 := by
  have hF := partitionSecondCircle_fourierCoeff_summable
  have hpoint := has_pointwise_sum_fourier_series_of_summable hF
    (0 : AddCircle (1 : ℝ))
  have hsum : HasSum (fourierCoeff partitionSecondCircle)
      (partitionSecondCircle (0 : AddCircle (1 : ℝ))) := by
    simpa only [fourier_eval_zero, smul_eq_mul, mul_one] using hpoint
  have hnat : Summable (fun n : ℕ => fourierCoeff partitionSecondCircle (n : ℤ)) :=
    hF.comp_injective (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℤ)))
  have hneg : Summable (fun n : ℕ => fourierCoeff partitionSecondCircle (-(n + 1 : ℤ))) :=
    hF.comp_injective (show Function.Injective (fun n : ℕ => -(n + 1 : ℤ)) by
      intro a b hab
      have hh : (a : ℤ) + 1 = (b : ℤ) + 1 := neg_injective hab
      omega)
  have he : (∑' j : ℤ, fourierCoeff partitionSecondCircle j) =
      2 * (↑(∑' n, partitionFourierCoefficient n) : ℂ) := by
    rw [tsum_of_nat_of_neg_add_one hnat hneg, hnat.tsum_eq_zero_add,
      Nat.cast_zero, partitionSecondCircle_fourierCoeff_zero, zero_add]
    have hp (n : ℕ) : fourierCoeff partitionSecondCircle ((n + 1 : ℕ) : ℤ) =
        (partitionFourierCoefficient n : ℂ) := partitionSecondCircle_fourierCoeff_pos n
    have hm (n : ℕ) : fourierCoeff partitionSecondCircle (-(n + 1 : ℤ)) =
        (partitionFourierCoefficient n : ℂ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using partitionSecondCircle_fourierCoeff_neg n
    simp_rw [hp, hm, ← Complex.ofReal_tsum]
    ring
  have hv := hsum.tsum_eq
  rw [he, partitionSecondCircle_zero] at hv
  have hr := congrArg Complex.re hv
  norm_num at hr
  nlinarith

end
end CGLMPBounds.Partition
