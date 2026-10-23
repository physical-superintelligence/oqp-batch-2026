module

public import CGLMPBounds.Partition.CharacterIntegrals

@[expose] public section


/-! Normalization of the actual single Fourier-power boundary density.
The proof expands the literal squared sum and integrates its actual coordinate
pairs. No mean-one or independence hypothesis is added to the definition. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

lemma boundaryCharacter_mul_star_self (n : ℕ) (t : ℝ) :
    boundaryCharacter n t * star (boundaryCharacter n t) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    boundaryCharacter_norm]
  norm_num

lemma integrable_boundaryCharacter_pair (d n : ℕ) (i j : Fin d) :
    Integrable (fun T : Fin d → ℝ =>
      boundaryCharacter n (T i) * star (boundaryCharacter n (T j)))
      (boundaryProductMeasure d) := by
  apply (integrable_const (1 : ℝ)).mono'
    (((continuous_boundaryCharacter n).comp (continuous_apply i)).mul
      (continuous_star.comp
        ((continuous_boundaryCharacter n).comp (continuous_apply j)))).aestronglyMeasurable
  filter_upwards [] with T
  simp [norm_mul, boundaryCharacter_norm]

lemma integral_boundaryCharacter_coordinate (d n : ℕ) (hn : 0 < n) (i : Fin d) :
    ∫ T : Fin d → ℝ, boundaryCharacter n (T i) ∂boundaryProductMeasure d = 0 := by
  unfold boundaryProductMeasure
  rw [integral_comp_eval (continuous_boundaryCharacter n).aestronglyMeasurable]
  exact integral_boundaryCharacter_uniform n hn

/-- Actual coordinate orthogonality: the diagonal contributes one and each
off-diagonal pair integrates to zero under the literal product measure. -/
theorem integral_boundaryCharacter_pair (d n : ℕ) (hn : 0 < n) (i j : Fin d) :
    (∫ T : Fin d → ℝ,
      boundaryCharacter n (T i) * star (boundaryCharacter n (T j))
        ∂boundaryProductMeasure d) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [boundaryCharacter_mul_star_self]
    simp
  · have hX : Continuous (fun T : Fin d → ℝ => boundaryCharacter n (T i)) :=
      (continuous_boundaryCharacter n).comp (continuous_apply i)
    have hY : Continuous (fun T : Fin d → ℝ => star (boundaryCharacter n (T j))) :=
      continuous_star.comp ((continuous_boundaryCharacter n).comp (continuous_apply j))
    have hIndep := ((boundary_coordinates_independent d).indepFun hij).comp
      (continuous_boundaryCharacter n).measurable
      (continuous_star.comp (continuous_boundaryCharacter n)).measurable
    have hprod := hIndep.integral_fun_mul_eq_mul_integral
      hX.aestronglyMeasurable hY.aestronglyMeasurable
    simpa only [Function.comp_apply, integral_boundaryCharacter_coordinate d n hn i,
      zero_mul, if_neg hij] using hprod

lemma fourierBoundaryDensity_complex_expansion (d n : ℕ) (T : Fin d → ℝ) :
    (fourierBoundaryDensity d n T : ℂ) =
      (∑ i : Fin d, ∑ j : Fin d,
        boundaryCharacter n (T i) * star (boundaryCharacter n (T j))) / (d : ℂ) := by
  have hnorm : ((‖∑ i : Fin d, boundaryCharacter n (T i)‖ ^ 2 : ℝ) : ℂ) =
      (∑ i : Fin d, boundaryCharacter n (T i)) *
        star (∑ i : Fin d, boundaryCharacter n (T i)) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [fourierBoundaryDensity, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [hnorm]
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- The factor 1/d is justified by actual product-measure integration. The
positive-frequency hypothesis is essential: the zero mode has density d. -/
theorem integral_fourierBoundaryDensity (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    ∫ T, fourierBoundaryDensity d n T ∂boundaryProductMeasure d = 1 := by
  classical
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    (∫ T, (fourierBoundaryDensity d n T : ℂ) ∂boundaryProductMeasure d) =
        (∫ T, (∑ i : Fin d, ∑ j : Fin d,
          boundaryCharacter n (T i) * star (boundaryCharacter n (T j))) / (d : ℂ)
            ∂boundaryProductMeasure d) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fourierBoundaryDensity_complex_expansion d n)
    _ = (∑ i : Fin d, ∑ j : Fin d,
        ∫ T : Fin d → ℝ,
          boundaryCharacter n (T i) * star (boundaryCharacter n (T j))
            ∂boundaryProductMeasure d) / (d : ℂ) := by
      rw [integral_div]
      congr 1
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => integrable_boundaryCharacter_pair d n i j))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum Finset.univ (fun j _ => integrable_boundaryCharacter_pair d n i j)
    _ = (1 : ℂ) := by
      simp_rw [integral_boundaryCharacter_pair d n hn]
      simp [hdC]

theorem fourierBoundaryMeasure_isProbabilityMeasure
    (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    IsProbabilityMeasure (fourierBoundaryMeasure d n) := by
  refine ⟨?_⟩
  rw [fourierBoundaryMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_fourierBoundaryDensity d n)
      (Filter.Eventually.of_forall (fourierBoundaryDensity_nonneg d n)),
    integral_fourierBoundaryDensity d n hd hn]
  simp

end
end CGLMPBounds.Partition
