module

public import CGLMPBounds.Partition.CharacterIntegrals

@[expose] public section


/-! Pointwise circular rotation of the actual Fourier-power density.
This file does not assume or assert measure preservation of rotation. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

lemma boundaryCharacter_sub (n : ℕ) (t u : ℝ) :
    boundaryCharacter n (t - u) = boundaryCharacter n t / boundaryCharacter n u := by
  unfold boundaryCharacter
  rw [← Complex.exp_sub]
  congr 1
  push_cast
  ring

lemma boundaryCharacter_intCast (n : ℕ) (m : ℤ) :
    boundaryCharacter n (m : ℝ) = 1 := by
  calc
    boundaryCharacter n (m : ℝ) =
        Complex.exp (((m * (n : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
      unfold boundaryCharacter
      congr 1
      push_cast
      ring
    _ = 1 := Complex.exp_int_mul_two_pi_mul_I (m * (n : ℤ))

lemma boundaryCharacter_fract (n : ℕ) (t : ℝ) :
    boundaryCharacter n (Int.fract t) = boundaryCharacter n t := by
  rw [Int.fract, boundaryCharacter_sub, boundaryCharacter_intCast, div_one]

lemma boundaryCharacter_rotate (n : ℕ) (origin t : ℝ) :
    boundaryCharacter n (Int.fract (t - origin)) =
      boundaryCharacter n t / boundaryCharacter n origin := by
  rw [boundaryCharacter_fract, boundaryCharacter_sub]

/-- The modulus square removes the common phase introduced by rotation.
This identity holds for all d,n, including the empty and zero-frequency cases. -/
theorem fourierBoundaryDensity_rotate (d n : ℕ) (origin : ℝ) (T : Fin d → ℝ) :
    fourierBoundaryDensity d n (rotateBoundaryPoints d origin T) =
      fourierBoundaryDensity d n T := by
  simp only [fourierBoundaryDensity, rotateBoundaryPoints, boundaryCharacter_rotate,
    ← Finset.sum_div, norm_div, boundaryCharacter_norm, div_one]

end
end CGLMPBounds.Partition
