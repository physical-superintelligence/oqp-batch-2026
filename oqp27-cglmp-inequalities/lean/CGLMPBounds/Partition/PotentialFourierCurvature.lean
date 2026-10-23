module

public import CGLMPBounds.Partition.PotentialFourierMass
public import CGLMPBounds.Partition.MixtureDerivatives

@[expose] public section


/-! Genuine pointwise Fourier reconstruction of the actual second derivative.
The integer-indexed complex Fourier series is paired into the positive real
cosine frequencies used in D.9. -/

namespace CGLMPBounds.Partition
open Set
open scoped Topology
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private lemma source_fourier_pair (n : ℕ) (x : ℝ) :
    fourierCoeff partitionSecondCircle ((n + 1 : ℕ) : ℤ) *
        fourier ((n + 1 : ℕ) : ℤ) (x : AddCircle (1 : ℝ)) +
      fourierCoeff partitionSecondCircle (-((n + 1 : ℕ) : ℤ)) *
        fourier (-((n + 1 : ℕ) : ℤ)) (x : AddCircle (1 : ℝ)) =
      ((partitionFourierCoefficient n *
        (2 * Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x)) : ℝ) : ℂ) := by
  rw [partitionSecondCircle_fourierCoeff_pos, partitionSecondCircle_fourierCoeff_neg,
    fourier_coe_apply, fourier_coe_apply]
  have hp : 2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℤ) * (x : ℂ) / (1 : ℝ) =
      ((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hm : 2 * (Real.pi : ℂ) * Complex.I * (-((n + 1 : ℕ) : ℤ)) * (x : ℂ) / (1 : ℝ) =
      ((-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  simp only [Int.cast_neg]
  rw [hp, hm, Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

lemma partitionSecondCircle_eq_curvature (x : ℝ) :
    partitionSecondCircle (x : AddCircle (1 : ℝ)) =
      (fourierMixtureCurvature partitionFourierCoefficient x : ℂ) := by
  have hp := has_pointwise_sum_fourier_series_of_summable
    partitionSecondCircle_fourierCoeff_summable (x : AddCircle (1 : ℝ))
  let f : ℤ → ℂ := fun j => fourierCoeff partitionSecondCircle j *
    fourier j (x : AddCircle (1 : ℝ))
  have hsum : HasSum f (partitionSecondCircle (x : AddCircle (1 : ℝ))) := by
    simpa only [f, smul_eq_mul] using hp
  have hnat : Summable (fun n : ℕ => f n) :=
    hsum.summable.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => f (-(n + 1))) :=
    hsum.summable.comp_injective (show Function.Injective (fun n : ℕ => -(n + 1 : ℤ)) by
      intro a b hab
      have hh : (a : ℤ) + 1 = (b : ℤ) + 1 := neg_injective hab
      omega)
  have hpos : Summable (fun n : ℕ => f ((n + 1 : ℕ) : ℤ)) :=
    (summable_nat_add_iff 1).2 hnat
  have hzero : f 0 = 0 := by simp [f, partitionSecondCircle_fourierCoeff_zero]
  rw [← hsum.tsum_eq, tsum_of_nat_of_neg_add_one hnat hneg,
    hnat.tsum_eq_zero_add, Nat.cast_zero, hzero, zero_add, ← hpos.tsum_add hneg]
  unfold fourierMixtureCurvature
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simpa only [f, Nat.cast_add, Nat.cast_one] using source_fourier_pair n x

/-- Source v'' is the actual curvature of its literal positive mixture. -/
theorem partitionPotentialSecond_eq_curvature {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    partitionPotentialSecond x = fourierMixtureCurvature partitionFourierCoefficient x := by
  have hcircle : partitionSecondCircle (x : AddCircle (1 : ℝ)) =
      (partitionPotentialSecond x : ℂ) := by
    by_cases hx1 : x = 1
    · subst x
      have hcoe : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by simp
      rw [hcoe, ← partitionPotentialSecond_endpoints]
      change AddCircle.liftIco 1 0 (fun t => (partitionPotentialSecond t : ℂ))
        ((0 : ℝ) : AddCircle (1 : ℝ)) = _
      rw [AddCircle.liftIco_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 (0 + 1))]
    · change AddCircle.liftIco 1 0 (fun t => (partitionPotentialSecond t : ℂ))
        (x : AddCircle (1 : ℝ)) = _
      rw [AddCircle.liftIco_coe_apply (show x ∈ Ico 0 (0 + 1) from
        ⟨hx.1, by simpa using lt_of_le_of_ne hx.2 hx1⟩)]
  have he := partitionSecondCircle_eq_curvature x
  rw [hcircle] at he
  exact_mod_cast he

end
end CGLMPBounds.Partition
