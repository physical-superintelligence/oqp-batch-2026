module

public import CGLMPBounds.Partition.CountProduct
public import CGLMPBounds.Partition.DensityNormalization

@[expose] public section


/-! Exact finite-product integration with two distinguished boundary
coordinates. This derives the actual off-diagonal term in the Fourier-tilted
count generating function. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

lemma prod_two_distinguished (d : ℕ) (i j : Fin d) (hij : i ≠ j) (A B C : ℂ) :
    (∏ k : Fin d, if k = i then A else if k = j then B else C) =
      A * B * C ^ (d - 2) := by
  classical
  let F : Fin d → ℂ := fun k => if k = i then A else if k = j then B else C
  have hj : j ∈ (Finset.univ : Finset (Fin d)).erase i := by simp [hij.symm]
  have hrest : (∏ k ∈ ((Finset.univ : Finset (Fin d)).erase i).erase j, F k) =
      C ^ (d - 2) := by
    calc
      _ = ∏ _k ∈ ((Finset.univ : Finset (Fin d)).erase i).erase j, C := by
        apply Finset.prod_congr rfl
        intro k hk
        have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
        have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
        simp [F, hki, hkj]
      _ = _ := by
        simp only [Finset.prod_const, Finset.card_erase_of_mem hj,
          Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
        congr 1
  change (∏ k : Fin d, F k) = _
  rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) F hj, hrest]
  simp [F, hij.symm, mul_assoc]

/-- Product Fubini with two distinguished factors; this uses the actual
product measure and makes no distributional hypothesis. -/
theorem integral_prod_two_distinguished (d : ℕ) (i j : Fin d) (hij : i ≠ j)
    (g f h : ℝ → ℂ) :
    (∫ T : Fin d → ℝ, (∏ k : Fin d, g (T k)) * f (T i) * h (T j)
      ∂boundaryProductMeasure d) =
      (∫ t, g t * f t ∂boundaryUniformMeasure) *
        (∫ t, g t * h t ∂boundaryUniformMeasure) *
          (∫ t, g t ∂boundaryUniformMeasure) ^ (d - 2) := by
  classical
  let q : Fin d → ℝ → ℂ := fun k t =>
    g t * (if k = i then f t else 1) * (if k = j then h t else 1)
  have hfactor (T : Fin d → ℝ) :
      (∏ k : Fin d, g (T k)) * f (T i) * h (T j) = ∏ k : Fin d, q k (T k) := by
    simp only [q, Finset.prod_mul_distrib]
    simp
  calc
    _ = ∫ T : Fin d → ℝ, ∏ k : Fin d, q k (T k) ∂boundaryProductMeasure d := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hfactor
    _ = ∏ k : Fin d, ∫ t, q k t ∂boundaryUniformMeasure :=
      integral_fintype_prod_eq_prod q
    _ = ∏ k : Fin d,
        if k = i then (∫ t, g t * f t ∂boundaryUniformMeasure)
        else if k = j then (∫ t, g t * h t ∂boundaryUniformMeasure)
        else (∫ t, g t ∂boundaryUniformMeasure) := by
      apply Finset.prod_congr rfl
      intro k hk
      by_cases hki : k = i
      · subst k
        simp [q, hij]
      · by_cases hkj : k = j
        · subst k
          simp [q, hij.symm]
        · simp [q, hki, hkj]
    _ = _ := prod_two_distinguished d i j hij _ _ _

theorem integral_count_character_pair_offdiag
    (d n : ℕ) (hn : 0 < n) (i j : Fin d) (hij : i ≠ j)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) :
    (∫ T : Fin d → ℝ, z ^ boundaryArcCount d 0 x T *
      boundaryCharacter n (T i) * star (boundaryCharacter n (T j))
        ∂boundaryProductMeasure d) =
      (z - 1) ^ 2 * (fourierTiltShape n x : ℂ) *
        (1 - (x : ℂ) + (x : ℂ) * z) ^ (d - 2) := by
  calc
    _ = ∫ T : Fin d → ℝ,
        (∏ k : Fin d, if T k < x then z else 1) *
          boundaryCharacter n (T i) * star (boundaryCharacter n (T j))
            ∂boundaryProductMeasure d := by
      apply integral_congr_ae
      filter_upwards [boundaryArcCount_zero_pow_ae_prod d x z] with T hT
      rw [hT]
    _ = _ := by
      rw [integral_prod_two_distinguished d i j hij
        (fun t => if t < x then z else 1) (boundaryCharacter n)
        (fun t => star (boundaryCharacter n t)),
        arcFactor_character_integrals_product n hn x hx z, integral_arcFactor x hx z]

theorem integral_count_character_pair
    (d n : ℕ) (hn : 0 < n) (i j : Fin d)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) :
    (∫ T : Fin d → ℝ, z ^ boundaryArcCount d 0 x T *
      boundaryCharacter n (T i) * star (boundaryCharacter n (T j))
        ∂boundaryProductMeasure d) =
      if i = j then (1 - (x : ℂ) + (x : ℂ) * z) ^ d
      else (z - 1) ^ 2 * (fourierTiltShape n x : ℂ) *
        (1 - (x : ℂ) + (x : ℂ) * z) ^ (d - 2) := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl, mul_assoc, boundaryCharacter_mul_star_self, mul_one]
    exact integral_boundaryArcCount_zero_pow d x hx z
  · rw [if_neg hij]
    exact integral_count_character_pair_offdiag d n hn i j hij x hx z

theorem integrable_count_character_pair
    (d n : ℕ) (i j : Fin d) (x : ℝ) (z : ℂ) :
    Integrable (fun T : Fin d → ℝ => z ^ boundaryArcCount d 0 x T *
      boundaryCharacter n (T i) * star (boundaryCharacter n (T j)))
      (boundaryProductMeasure d) := by
  have hfirst := (integrable_boundaryArcCount_zero_pow d x z).mul_bdd
    ((continuous_boundaryCharacter n).comp (continuous_apply i)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun T : Fin d → ℝ =>
      (boundaryCharacter_norm n (T i)).le))
  exact hfirst.mul_bdd (c := 1)
    (continuous_star.comp
      ((continuous_boundaryCharacter n).comp (continuous_apply j))).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun T : Fin d → ℝ => by
      simp [boundaryCharacter_norm]))

end
end CGLMPBounds.Partition
