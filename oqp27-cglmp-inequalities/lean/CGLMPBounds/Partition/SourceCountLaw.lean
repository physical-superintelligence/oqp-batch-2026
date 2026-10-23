module

public import CGLMPBounds.Defs.PartitionSource
public import CGLMPBounds.Partition.PotentialFourierIdentity
public import CGLMPBounds.Partition.MixturePairDensity

@[expose] public section


/-! The source-specific probability density and exact D.11 count law.
Every Fourier sign, convergence, mass and reconstruction input is supplied
by a theorem about the literal source potential. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

lemma sourcePartitionResidual :
    fourierMixtureResidual partitionFourierCoefficient = 3 / 2 - Real.pi / 4 := by
  rw [fourierMixtureResidual, partitionFourierCoefficient_tsum]
  ring

lemma sourcePartitionCoefficientMass_lt_one : (∑' n, partitionFourierCoefficient n) < 1 := by
  rw [partitionFourierCoefficient_tsum]
  linarith [Real.pi_lt_four]

theorem sourcePartitionDensity_lower (d : ℕ) (T : Fin d → ℝ) :
    3 / 2 - Real.pi / 4 ≤ sourcePartitionDensity d T := by
  rw [← sourcePartitionResidual]
  exact fourierMixtureDensity_lower d partitionFourierCoefficient
    (fun n => (partitionFourierCoefficient_pos n).le) T

theorem sourcePartitionDensity_pos (d : ℕ) (T : Fin d → ℝ) :
    0 < sourcePartitionDensity d T := by
  have h := sourcePartitionDensity_lower d T
  linarith [Real.pi_lt_four]

theorem sourcePartitionMeasure_isProbabilityMeasure (d : ℕ) (hd : 0 < d) :
    IsProbabilityMeasure (sourcePartitionMeasure d) :=
  fourierMixtureMeasure_isProbabilityMeasure d hd partitionFourierCoefficient
    (fun n => (partitionFourierCoefficient_pos n).le) partitionFourierCoefficient_summable
    sourcePartitionCoefficientMass_lt_one.le

/-- D.11 for the actual random boundary points and literal D.5 potential.
All origins, interval lengths in [0,1], and natural count values are covered. -/
theorem sourcePartitionMeasure_count_law (d h : ℕ) (hd : 2 ≤ d) (origin x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (sourcePartitionMeasure d).real {T | boundaryArcCount d origin x T = h} =
      scalarBinomialWeight d h x + partitionPotential x / d *
        iteratedDeriv 2 (scalarBinomialWeight d h) x := by
  rw [sourcePartitionMeasure, fourierMixtureMeasure_count_law d h hd partitionFourierCoefficient
    (fun n => (partitionFourierCoefficient_pos n).le) partitionFourierCoefficient_summable
    sourcePartitionCoefficientMass_lt_one.le origin x hx, partitionPotential_fourier x hx]

lemma fourierMixtureCurvature_fract (a : ℕ → ℝ) (x : ℝ) :
    fourierMixtureCurvature a (Int.fract x) = fourierMixtureCurvature a x := by
  unfold fourierMixtureCurvature
  apply tsum_congr
  intro n
  have hangle : 2 * Real.pi * ((n + 1 : ℕ) : ℝ) * Int.fract x =
      2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x -
        (((n + 1 : ℕ) : ℤ) * Int.floor x : ℤ) * (2 * Real.pi) := by
    rw [Int.fract]
    push_cast
    ring
  rw [hangle, Real.cos_sub_int_mul_two_pi]

lemma sourcePeriodicCurvature_eq_mixture (x : ℝ) :
    sourcePeriodicCurvature x = fourierMixtureCurvature partitionFourierCoefficient x := by
  change partitionPotentialSecond (Int.fract x) = _
  rw [partitionPotentialSecond_eq_curvature
    (show Int.fract x ∈ Set.Icc (0 : ℝ) 1 from
      ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩), fourierMixtureCurvature_fract]

/-- D.10's actual pair-curvature form, with periodic interpretation explicit. -/
theorem sourcePartitionDensity_pair_curvature (d : ℕ) (hd : 0 < d) (T : Fin d → ℝ) :
    sourcePartitionDensity d T = 1 + (1 / (d : ℝ)) *
      ∑ i : Fin d, ∑ j : Fin d,
        if i < j then sourcePeriodicCurvature (T i - T j) else 0 := by
  rw [sourcePartitionDensity, fourierMixtureDensity_pair_curvature d hd partitionFourierCoefficient
    (fun n => (partitionFourierCoefficient_pos n).le) partitionFourierCoefficient_summable]
  simp_rw [sourcePeriodicCurvature_eq_mixture]

end
end CGLMPBounds.Partition
