module

public import CGLMPBounds.Partition.PotentialProductRegularity
public import CGLMPBounds.Partition.SecondIntegrationByParts

@[expose] public section


/-! The two actual integrations by parts between D.11 and D.7–D.8.
The smooth removable product and the binomial endpoint zeros discharge
all boundary terms. This does not assume partition-form positivity. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
noncomputable section

/-- Exact weighted correction under the literal count law. -/
theorem potential_binomial_second_transfer (d h : ℕ) (hh0 : 0 < h) (hhd : h < d) :
    (∫ x in (0 : ℝ)..1, partitionPotential x * scalarSecant x *
      iteratedDeriv 2 (scalarBinomialWeight d h) x) =
      ∫ x in (0 : ℝ)..1, scalarBinomialWeight d h x *
        (scalarCorrectionB x - scalarPartitionS x) := by
  have hp : ContDiff ℝ ⊤ (scalarBinomialWeight d h) := by
    unfold scalarBinomialWeight
    fun_prop
  have hp0 : scalarBinomialWeight d h 0 = 0 := by
    simp [scalarBinomialWeight, zero_pow (Nat.ne_of_gt hh0)]
  have hp1 : scalarBinomialWeight d h 1 = 0 := by
    have hdh : d - h ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hhd)
    simp [scalarBinomialWeight, zero_pow hdh]
  have htransfer := integral_second_within_transfer potential_secant_product_contDiffOn
    hp.contDiffOn (by simp) (by simp) hp0 hp1
  have hleft : (∫ x in (0 : ℝ)..1, partitionPotential x * scalarSecant x *
      iteratedDerivWithin 2 (scalarBinomialWeight d h) (Icc (0 : ℝ) 1) x) =
      ∫ x in (0 : ℝ)..1, partitionPotential x * scalarSecant x *
        iteratedDeriv 2 (scalarBinomialWeight d h) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    change partitionPotential x * scalarSecant x *
      iteratedDerivWithin 2 (scalarBinomialWeight d h) (Icc (0 : ℝ) 1) x =
      partitionPotential x * scalarSecant x * iteratedDeriv 2 (scalarBinomialWeight d h) x
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) (hp.contDiffAt.of_le (by simp)) hx']
  rw [hleft] at htransfer
  rw [htransfer]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
  intro x hx
  have hprod : ContDiffAt ℝ 2 (fun t => partitionPotential t * scalarSecant t) x :=
    (potential_secant_product_contDiffOn.contDiffAt (Icc_mem_nhds hx.1 hx.2)).of_le (by simp)
  change scalarBinomialWeight d h x *
    iteratedDerivWithin 2 (fun t => partitionPotential t * scalarSecant t) (Icc (0 : ℝ) 1) x =
    scalarBinomialWeight d h x * (scalarCorrectionB x - scalarPartitionS x)
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hprod ⟨hx.1.le, hx.2.le⟩,
    potential_secant_product_second hx]

end
end CGLMPBounds.Partition
