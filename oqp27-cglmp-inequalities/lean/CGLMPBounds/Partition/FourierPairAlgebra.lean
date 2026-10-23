module

public import CGLMPBounds.Partition.CharacterRotation
public import CGLMPBounds.Partition.DensityNormalization

@[expose] public section


/-! Exact real pair expansion of the actual Fourier-power density.
The upper-triangle sum uses the literal order on Fin d. -/

namespace CGLMPBounds.Partition
noncomputable section

lemma sum_sum_symmetric_eq_diag_add_twice (d : ℕ) (f : Fin d → Fin d → ℝ)
    (hsym : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) +
      2 * ∑ i, ∑ j, if i < j then f i j else 0 := by
  classical
  have hcell (i j : Fin d) : f i j =
      (if i = j then f i i else 0) +
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j
      simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hswap : (∑ i : Fin d, ∑ j : Fin d, if j < i then f i j else 0) =
      ∑ i : Fin d, ∑ j : Fin d, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  calc
    _ = ∑ i : Fin d, ∑ j : Fin d,
        ((if i = j then f i i else 0) +
          (if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun j hj => hcell i j)
    _ = (∑ i, f i i) + (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by
      simp only [Finset.sum_add_distrib]
      simp
    _ = _ := by rw [hswap]; ring

lemma boundaryCharacter_mul_star (n : ℕ) (t u : ℝ) :
    boundaryCharacter n t * star (boundaryCharacter n u) =
      boundaryCharacter n (t - u) := by
  have hu : boundaryCharacter n u ≠ 0 := by
    intro h
    have hn := boundaryCharacter_norm n u
    rw [h, norm_zero] at hn
    norm_num at hn
  rw [boundaryCharacter_sub]
  apply (eq_div_iff hu).mpr
  rw [mul_assoc, mul_comm (star (boundaryCharacter n u)) (boundaryCharacter n u),
    boundaryCharacter_mul_star_self, mul_one]

lemma boundaryCharacter_mul_star_re (n : ℕ) (t u : ℝ) :
    (boundaryCharacter n t * star (boundaryCharacter n u)).re =
      Real.cos (2 * Real.pi * (n : ℝ) * (t - u)) := by
  rw [boundaryCharacter_mul_star]
  simp only [boundaryCharacter, Complex.exp_ofReal_mul_I_re]

lemma fourierBoundaryDensity_real_expansion (d n : ℕ) (T : Fin d → ℝ) :
    fourierBoundaryDensity d n T =
      (∑ i : Fin d, ∑ j : Fin d,
        Real.cos (2 * Real.pi * (n : ℝ) * (T i - T j))) / d := by
  have h := congrArg Complex.re (fourierBoundaryDensity_complex_expansion d n T)
  simpa only [Complex.ofReal_re, Complex.div_natCast_re, Complex.re_sum,
    boundaryCharacter_mul_star_re] using h

theorem fourierBoundaryDensity_pair_expansion (d n : ℕ) (hd : 0 < d)
    (T : Fin d → ℝ) :
    fourierBoundaryDensity d n T = 1 + (2 / (d : ℝ)) *
      ∑ i : Fin d, ∑ j : Fin d,
        if i < j then Real.cos (2 * Real.pi * (n : ℝ) * (T i - T j)) else 0 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hsym (i j : Fin d) :
      Real.cos (2 * Real.pi * (n : ℝ) * (T i - T j)) =
        Real.cos (2 * Real.pi * (n : ℝ) * (T j - T i)) := by
    rw [show 2 * Real.pi * (n : ℝ) * (T j - T i) =
      -(2 * Real.pi * (n : ℝ) * (T i - T j)) by ring, Real.cos_neg]
  rw [fourierBoundaryDensity_real_expansion,
    sum_sum_symmetric_eq_diag_add_twice d _ hsym]
  simp only [sub_self, mul_zero, Real.cos_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp [hd0]

end
end CGLMPBounds.Partition
