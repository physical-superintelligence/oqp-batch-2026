module

public import CGLMPBounds.Partition.CharacterIntegrals

@[expose] public section


/-! Actual one-coordinate integrals underlying the D.3 count generating
function. The arc is the literal interval [0,x), represented on [0,1) by
the predicate t<x. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

lemma boundaryUniformMeasure_restrict_Iio {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    boundaryUniformMeasure.restrict (Set.Iio x) = volume.restrict (Set.Ico (0 : ℝ) x) := by
  have hset : Set.Iio x ∩ Set.Ico (0 : ℝ) 1 = Set.Ico (0 : ℝ) x := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
    constructor
    · intro h
      exact ⟨h.2.1, h.1⟩
    · intro h
      exact ⟨h.2, h.1, lt_of_lt_of_le h.2 hx.2⟩
  rw [boundaryUniformMeasure, Measure.restrict_restrict measurableSet_Iio, hset]

/-- The generic one-coordinate tilt integral is derived from an indicator,
without assuming a count distribution. -/
theorem integral_arcFactor_mul {f : ℝ → ℂ}
    (hf : Integrable f boundaryUniformMeasure) (x : ℝ) (z : ℂ) :
    (∫ t, (if t < x then z else 1) * f t ∂boundaryUniformMeasure) =
      (∫ t, f t ∂boundaryUniformMeasure) +
        (z - 1) * ∫ t in Set.Iio x, f t ∂boundaryUniformMeasure := by
  classical
  have hfun : (fun t => (if t < x then z else 1) * f t) =
      (fun t => f t + (z - 1) * (Set.Iio x).indicator f t) := by
    funext t
    by_cases ht : t < x
    · simp [ht, Set.mem_Iio]
      ring
    · simp [ht, Set.mem_Iio]
  rw [hfun, integral_add hf ((hf.indicator measurableSet_Iio).const_mul (z - 1)),
    integral_const_mul, integral_indicator measurableSet_Iio]

theorem integral_arcFactor (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) :
    (∫ t : ℝ, (if t < x then z else 1) ∂boundaryUniformMeasure) =
      1 - (x : ℂ) + (x : ℂ) * z := by
  have hconst : (∫ t in Set.Iio x, (1 : ℂ) ∂boundaryUniformMeasure) = (x : ℂ) := by
    change (∫ _ : ℝ, (1 : ℂ) ∂boundaryUniformMeasure.restrict (Set.Iio x)) = _
    rw [boundaryUniformMeasure_restrict_Iio hx]
    simp [integral_const, measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal hx.1]
  have hone : (∫ _ : ℝ, (1 : ℂ) ∂boundaryUniformMeasure) = 1 := by
    simp [integral_const, measureReal_def]
  have h := integral_arcFactor_mul (integrable_const (1 : ℂ)) x z
  simp only [mul_one] at h
  rw [hone, hconst] at h
  rw [h]
  ring

lemma integral_boundaryCharacter_uniform_Iio
    (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ t in Set.Iio x, boundaryCharacter n t ∂boundaryUniformMeasure) =
      ∫ t in (0 : ℝ)..x, boundaryCharacter n t := by
  change (∫ t, boundaryCharacter n t
    ∂boundaryUniformMeasure.restrict (Set.Iio x)) = _
  rw [boundaryUniformMeasure_restrict_Iio hx]
  exact (integral_Ico_eq_integral_Ioc.trans (intervalIntegral.integral_of_le hx.1).symm)

theorem integral_arcFactor_mul_boundaryCharacter
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) :
    (∫ t, (if t < x then z else 1) * boundaryCharacter n t ∂boundaryUniformMeasure) =
      (z - 1) * ∫ t in (0 : ℝ)..x, boundaryCharacter n t := by
  rw [integral_arcFactor_mul (integrable_boundaryCharacter_uniform n),
    integral_boundaryCharacter_uniform n hn, integral_boundaryCharacter_uniform_Iio n x hx,
    zero_add]

theorem integral_arcFactor_mul_star_boundaryCharacter
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) :
    (∫ t, (if t < x then z else 1) * star (boundaryCharacter n t)
      ∂boundaryUniformMeasure) =
      (z - 1) * star (∫ t in (0 : ℝ)..x, boundaryCharacter n t) := by
  have hstar : Integrable (fun t => star (boundaryCharacter n t)) boundaryUniformMeasure := by
    apply (integrable_const (1 : ℝ)).mono'
      (continuous_star.comp (continuous_boundaryCharacter n)).aestronglyMeasurable
    filter_upwards [] with t
    simp [boundaryCharacter_norm]
  rw [integral_arcFactor_mul hstar]
  simp only [Complex.star_def, integral_conj]
  rw [integral_boundaryCharacter_uniform n hn,
    integral_boundaryCharacter_uniform_Iio n x hx]
  simp

/-- The off-diagonal Fourier correction has precisely the source sine-square
shape, with no conjugation of the complex generating variable z. -/
theorem arcFactor_character_integrals_product
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) :
    (∫ t, (if t < x then z else 1) * boundaryCharacter n t ∂boundaryUniformMeasure) *
      (∫ t, (if t < x then z else 1) * star (boundaryCharacter n t)
        ∂boundaryUniformMeasure) =
      (z - 1) ^ 2 * (fourierTiltShape n x : ℂ) := by
  rw [integral_arcFactor_mul_boundaryCharacter n hn x hx z,
    integral_arcFactor_mul_star_boundaryCharacter n hn x hx z]
  calc
    _ = (z - 1) ^ 2 * ((∫ t in (0 : ℝ)..x, boundaryCharacter n t) *
        star (∫ t in (0 : ℝ)..x, boundaryCharacter n t)) := by ring
    _ = _ := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        norm_intervalIntegral_boundaryCharacter_sq n hn x]

/-- Actual product integration of the unweighted arc factors. This is the
polynomial (1-x+xz)^d before identifying the product with z to the count. -/
theorem integral_prod_arcFactor (d : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) :
    (∫ T : Fin d → ℝ, ∏ j : Fin d, (if T j < x then z else 1)
      ∂boundaryProductMeasure d) = (1 - (x : ℂ) + (x : ℂ) * z) ^ d := by
  unfold boundaryProductMeasure
  rw [integral_fintype_prod_eq_prod (fun _ : Fin d => fun t : ℝ => if t < x then z else 1)]
  simp [integral_arcFactor x hx z]

end
end CGLMPBounds.Partition
