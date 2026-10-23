module

public import CGLMPBounds.Partition.PotentialFourierCurvature
public import CGLMPBounds.Partition.PotentialFourierPositive

@[expose] public section


/-! The literal D.5 potential equals its D.9 sine-square mixture.
Actual summable Fourier reconstruction supplies equality of the second
derivatives; two applications of the mean value theorem and the literal
zero initial value/derivative identify the functions. No source Fourier
identity is an assumption. -/

namespace CGLMPBounds.Partition
open Set
noncomputable section

private lemma eqOn_of_matching_derivatives {f g f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc (0 : ℝ) 1) x)
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (f' x) (Icc (0 : ℝ) 1) x)
    (hzero : f 0 = g 0) : EqOn f g (Icc (0 : ℝ) 1) := by
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun t => f t - g t) 0 (Icc (0 : ℝ) 1) x := by
    simpa only [sub_self] using! (hf x hx).fun_sub (hg x hx)
  intro x hx
  have hbound := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd (C := 0) (fun _ _ => by simp) (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) hx
  have hnorm : ‖(f x - g x) - (f 0 - g 0)‖ = 0 :=
    le_antisymm (by simpa using hbound) (norm_nonneg _)
  have he := norm_eq_zero.mp hnorm
  rw [hzero, sub_self, sub_zero] at he
  exact sub_eq_zero.mp he

lemma partitionPotential_firstWithin_eq_mixtureSlope {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin 1 partitionPotential (Icc (0 : ℝ) 1) x =
      fourierMixtureSlope partitionFourierCoefficient x := by
  refine eqOn_of_matching_derivatives
    (f := iteratedDerivWithin 1 partitionPotential (Icc (0 : ℝ) 1))
    (g := fourierMixtureSlope partitionFourierCoefficient)
    (f' := partitionPotentialSecond)
    ?_ ?_ ?_ hx
  · intro y hy
    exact partitionPotential_derivativeWithin_hasDerivWithinAt 1 hy
  · intro y hy
    rw [partitionPotentialSecond_eq_curvature hy]
    exact (hasDerivAt_fourierMixtureSlope partitionFourierCoefficient
      (fun n => (partitionFourierCoefficient_pos n).le)
      partitionFourierCoefficient_summable y).hasDerivWithinAt
  · rw [partitionPotential_firstWithin_zero]
    simp [fourierMixtureSlope, fourierTiltSlope]

/-- The source D.9 expansion with the actual integral coefficients and the
literal guarded D.5 potential, including both endpoints and the midpoint. -/
theorem partitionPotential_fourier (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    fourierMixtureShape partitionFourierCoefficient x = partitionPotential x := by
  symm
  refine eqOn_of_matching_derivatives
    (f := partitionPotential)
    (g := fourierMixtureShape partitionFourierCoefficient)
    (f' := iteratedDerivWithin 1 partitionPotential (Icc (0 : ℝ) 1))
    ?_ ?_ ?_ hx
  · intro y hy
    simpa only [iteratedDerivWithin_zero] using!
      partitionPotential_derivativeWithin_hasDerivWithinAt 0 hy
  · intro y hy
    rw [partitionPotential_firstWithin_eq_mixtureSlope hy]
    exact (hasDerivAt_fourierMixtureShape partitionFourierCoefficient
      (fun n => (partitionFourierCoefficient_pos n).le)
      partitionFourierCoefficient_summable y).hasDerivWithinAt
  · simp [partitionPotential_zero, fourierMixtureShape, fourierTiltShape]

end
end CGLMPBounds.Partition
