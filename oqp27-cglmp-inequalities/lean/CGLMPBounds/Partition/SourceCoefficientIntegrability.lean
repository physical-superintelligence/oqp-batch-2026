module

public import CGLMPBounds.Defs.PartitionCoefficient
public import CGLMPBounds.Partition.SourceCountLaw
public import CGLMPBounds.Partition.PotentialCoefficientMatching
public import CGLMPBounds.Certificates.ScalarIntegralError

@[expose] public section


/-! Actual secant-weighted integrability for D.3 and D.7. The endpoint pole
is cancelled by the binomial weight, while the tilted correction uses the
removable product proved smooth on [0,1]. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory CGLMPBounds.Certificates
noncomputable section

theorem binomial_secant_intervalIntegrable (d h : ℕ) (hh : h < d) :
    IntervalIntegrable (fun x => scalarBinomialWeight d h x * scalarSecant x)
      volume 0 1 := by
  have hp := (scalarBetaPole_intervalIntegrable d h hh).const_mul (2 / Real.pi)
  have hr := scalarBetaRegular_intervalIntegrable d h
  apply (hp.add hr).congr_uIoo
  intro x hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
  dsimp only
  rw [scalarSecant_eq_pole_add_series hx']
  ring

theorem binomial_correction_intervalIntegrable (d h : ℕ) :
    IntervalIntegrable (fun x => scalarBinomialWeight d h x * scalarCorrectionB x)
      volume 0 1 := by
  have hi := (scalarBetaPhi_intervalIntegrable d h 2).const_mul (-(1 : ℝ) / 2)
  apply hi.congr_uIoo
  intro x hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
  dsimp only
  rw [scalarCorrectionB_eq_series hx']
  ring

theorem potential_binomial_correction_intervalIntegrable (d h : ℕ) :
    IntervalIntegrable (fun x => partitionPotential x * scalarSecant x *
      iteratedDeriv 2 (scalarBinomialWeight d h) x) volume 0 1 := by
  have hp : ContDiff ℝ ⊤ (scalarBinomialWeight d h) := by
    unfold scalarBinomialWeight
    fun_prop
  exact (potential_secant_product_contDiffOn.continuousOn.mul
    ((hp.continuous_iteratedDeriv 2 (by simp)).continuousOn)).intervalIntegrable_of_Icc
      (by norm_num)

theorem sourcePartitionCount_weight_intervalIntegrable (d h : ℕ)
    (hh0 : 0 < h) (hhd : h < d) (origin : ℝ) :
    IntervalIntegrable (fun x => scalarSecant x *
      (sourcePartitionMeasure d).real {T | boundaryArcCount d origin x T = h})
      volume 0 1 := by
  have h0 := binomial_secant_intervalIntegrable d h hhd
  have h1 := (potential_binomial_correction_intervalIntegrable d h).const_mul (1 / (d : ℝ))
  apply (h0.add h1).congr_uIoo
  intro x hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
  dsimp only
  rw [sourcePartitionMeasure_count_law d h (by omega) origin x ⟨hx'.1.le, hx'.2.le⟩]
  ring

end
end CGLMPBounds.Partition
