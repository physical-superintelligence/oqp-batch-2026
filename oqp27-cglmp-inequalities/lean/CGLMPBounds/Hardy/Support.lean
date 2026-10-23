module

public import CGLMPBounds.Hardy.Pencil

@[expose] public section


/-!
# Exact spectral-interval support in Lemma C.3

The Hermitian spectral theorem is used only for Y. The pencil itself is never
assumed diagonalizable. Its density continues to sum all characteristic-polynomial
roots with algebraic multiplicity, including repeated and defective roots.
-/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Unitary
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma hermitian_shift_spectral {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) (y : ℝ) :
    Y - (y : ℂ) • (1 : Matrix ι ι ℂ) =
      conjStarAlgAut ℂ _ hY.eigenvectorUnitary
        (Matrix.diagonal fun i => ((hY.eigenvalues i - y : ℝ) : ℂ)) := by
  have hd : (Matrix.diagonal fun i => ((hY.eigenvalues i - y : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => (hY.eigenvalues i : ℂ)) -
        (y : ℂ) • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.diagonal_apply, Matrix.one_apply]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  rw [hd, map_sub, map_smul, map_one]
  change Y - (y : ℂ) • (1 : Matrix ι ι ℂ) =
    conjStarAlgAut ℂ _ hY.eigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues)) - (y : ℂ) • 1
  rw [← hY.spectral_theorem]

lemma neg_hermitian_shift_spectral {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) (y : ℝ) :
    -(Y - (y : ℂ) • (1 : Matrix ι ι ℂ)) =
      conjStarAlgAut ℂ _ hY.eigenvectorUnitary
        (Matrix.diagonal fun i => ((y - hY.eigenvalues i : ℝ) : ℂ)) := by
  have hd : (Matrix.diagonal fun i => ((y - hY.eigenvalues i : ℝ) : ℂ)) =
      -(Matrix.diagonal fun i => ((hY.eigenvalues i - y : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.diagonal_apply, sub_eq_neg_add, add_comm]
    · simp [Matrix.diagonal_apply, h]
  rw [hd, map_neg, ← hermitian_shift_spectral hY y]

lemma hermitian_shift_posDef_of_lt_eigenvalues {Y : Matrix ι ι ℂ}
    (hY : Y.IsHermitian) (y : ℝ) (hy : ∀ i, y < hY.eigenvalues i) :
    (Y - (y : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := by
  rw [hermitian_shift_spectral hY y, conjStarAlgAut_apply]
  apply (Unitary.isUnit_coe (U := hY.eigenvectorUnitary)).posDef_star_right_conjugate_iff.mpr
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast sub_pos.mpr (hy i)

lemma neg_hermitian_shift_posDef_of_eigenvalues_lt {Y : Matrix ι ι ℂ}
    (hY : Y.IsHermitian) (y : ℝ) (hy : ∀ i, hY.eigenvalues i < y) :
    (-(Y - (y : ℂ) • (1 : Matrix ι ι ℂ))).PosDef := by
  rw [neg_hermitian_shift_spectral hY y, conjStarAlgAut_apply]
  apply (Unitary.isUnit_coe (U := hY.eigenvectorUnitary)).posDef_star_right_conjugate_iff.mpr
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast sub_pos.mpr (hy i)

theorem traceDensity_eq_zero_of_lt_eigenvalues {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    (y : ℝ) (hy : ∀ i, y < hY.eigenvalues i) : traceDensity H Y y = 0 :=
  traceDensity_eq_zero_of_definite hH hdet y
    (Or.inl (hermitian_shift_posDef_of_lt_eigenvalues hY y hy))

theorem traceDensity_eq_zero_of_eigenvalues_lt {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    (y : ℝ) (hy : ∀ i, hY.eigenvalues i < y) : traceDensity H Y y = 0 :=
  traceDensity_eq_zero_of_definite hH hdet y
    (Or.inr (neg_hermitian_shift_posDef_of_eigenvalues_lt hY y hy))

/-- Every root contribution vanishes off the exact closed spectral interval of Y. -/
theorem traceDensity_eq_zero_outside_spectralInterval {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) {y : ℝ}
    (hy : y ∉ Set.Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y))) :
    traceDensity H Y y = 0 := by
  rw [hY.spectrum_real_eq_range_eigenvalues] at hy
  simp only [Set.mem_Icc, not_and_or, not_le] at hy
  rcases hy with hlow | hhigh
  · apply traceDensity_eq_zero_of_lt_eigenvalues hH hY hdet y
    intro i
    exact hlow.trans_le (csInf_le (Set.finite_range hY.eigenvalues).bddBelow ⟨i, rfl⟩)
  · apply traceDensity_eq_zero_of_eigenvalues_lt hH hY hdet y
    intro i
    exact (le_csSup (Set.finite_range hY.eigenvalues).bddAbove ⟨i, rfl⟩).trans_lt hhigh

/-- Ordinary support is contained in the interval between the least and greatest
real spectral values of Y, rather than merely in an unspecified compact set. -/
theorem traceDensity_support_subset_spectralInterval {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) :
    Function.support (traceDensity H Y) ⊆
      Set.Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y)) := by
  intro y hy
  by_contra hn
  exact hy (traceDensity_eq_zero_outside_spectralInterval hH hY hdet hn)

/-- The same exact interval contains the closed/topological support. -/
theorem traceDensity_tsupport_subset_spectralInterval {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) :
    tsupport (traceDensity H Y) ⊆
      Set.Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y)) :=
  closure_minimal (traceDensity_support_subset_spectralInterval hH hY hdet) isClosed_Icc

/-- Compact support does not require a prior continuity theorem for the density. -/
theorem traceDensity_hasCompactSupport {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) :
    HasCompactSupport (traceDensity H Y) := by
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (traceDensity_tsupport_subset_spectralInterval hH hY hdet)

end
end CGLMPBounds.Hardy
