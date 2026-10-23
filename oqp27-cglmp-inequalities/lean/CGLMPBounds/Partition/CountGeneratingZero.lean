module

public import CGLMPBounds.Partition.PairProduct

@[expose] public section


/-! The actual single-mode tilted count generating polynomial at origin zero.
All character moments and product-measure identities are derived in the
imported modules; none is an assumption of the endpoint. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

lemma sum_pair_choice (d : ℕ) (D E : ℂ) :
    (∑ i : Fin d, ∑ j : Fin d, if i = j then D else E) =
      (d : ℂ) * D + (d : ℂ) * ((d : ℂ) - 1) * E := by
  classical
  have hterm (i j : Fin d) : (if i = j then D else E) =
      E + (if i = j then D - E else 0) := by
    by_cases hij : i = j <;> simp [hij] <;> ring
  simp_rw [hterm]
  simp [Finset.sum_add_distrib, nsmul_eq_mul]
  ring

lemma fourierBoundaryDensity_count_complex_expansion
    (d n : ℕ) (x : ℝ) (z : ℂ) (T : Fin d → ℝ) :
    (fourierBoundaryDensity d n T : ℂ) * z ^ boundaryArcCount d 0 x T =
      (∑ i : Fin d, ∑ j : Fin d,
        z ^ boundaryArcCount d 0 x T * boundaryCharacter n (T i) *
          star (boundaryCharacter n (T j))) / (d : ℂ) := by
  rw [fourierBoundaryDensity_complex_expansion, div_mul_eq_mul_div]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The exact source single-mode generating polynomial, proved for the
literal arc starting at zero. Rotation preservation is a separate obligation. -/
theorem fourierBoundaryDensity_count_generating_zero (d n : ℕ)
    (hd : 2 ≤ d) (hn : 0 < n) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) :
    (∫ T, (fourierBoundaryDensity d n T : ℂ) * z ^ boundaryArcCount d 0 x T
      ∂boundaryProductMeasure d) =
      (((1 - x : ℝ) : ℂ) + (x : ℂ) * z) ^ d +
        ((d : ℂ) - 1) * (fourierTiltShape n x : ℂ) * (z - 1) ^ 2 *
          (((1 - x : ℝ) : ℂ) + (x : ℂ) * z) ^ (d - 2) := by
  classical
  have hdC : (d : ℂ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by omega)
  calc
    _ = (∫ T : Fin d → ℝ, (∑ i : Fin d, ∑ j : Fin d,
        z ^ boundaryArcCount d 0 x T * boundaryCharacter n (T i) *
          star (boundaryCharacter n (T j))) / (d : ℂ)
            ∂boundaryProductMeasure d) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fourierBoundaryDensity_count_complex_expansion d n x z)
    _ = (∑ i : Fin d, ∑ j : Fin d,
        ∫ T : Fin d → ℝ, z ^ boundaryArcCount d 0 x T *
          boundaryCharacter n (T i) * star (boundaryCharacter n (T j))
            ∂boundaryProductMeasure d) / (d : ℂ) := by
      rw [integral_div]
      congr 1
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ =>
          integrable_count_character_pair d n i j x z))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum Finset.univ (fun j _ =>
        integrable_count_character_pair d n i j x z)
    _ = _ := by
      simp_rw [integral_count_character_pair d n hn _ _ x hx z]
      rw [sum_pair_choice]
      push_cast
      field_simp [hdC]
      <;> ring

end
end CGLMPBounds.Partition
