module

public import ThreeCopyQutritWerner.PositiveRankTwo

@[expose] public section


/-! Actual one-ray spectral decomposition, including no ambient-size premise. -/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

/-- A nonzero positive matrix of rank at most one has one actual unit spectral
ray and a strictly positive real weight. -/
theorem posSemidef_rank_le_one_exists_positive_ray {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (hP : P.PosSemidef) (hr : P.rank ≤ 1) (hne : P ≠ 0) :
    ∃ (u : n → ℂ) (lam : ℝ), vecNormSq u = 1 ∧ 0 < lam ∧
      P = (lam : ℂ) • ketBra u u := by
  classical
  let s := Finset.univ.filter (fun k => hP.isHermitian.eigenvalues k ≠ 0)
  have hs : s.card ≤ 1 := by
    have he : s.card = P.rank := by
      rw [hP.isHermitian.rank_eq_card_non_zero_eigs]
      simp [s, Fintype.card_subtype]
    exact he.trans_le hr
  have hsne : s.Nonempty := by
    by_contra h
    apply hne
    ext i j
    rw [hermitian_spectral_entry P hP.isHermitian i j]
    apply Finset.sum_eq_zero
    intro k _
    have hk : hP.isHermitian.eigenvalues k = 0 := by
      by_contra hk
      exact h ⟨k, by simp [s, hk]⟩
    simp [hk]
  obtain ⟨i, hi⟩ := hsne
  have hi0 : hP.isHermitian.eigenvalues i ≠ 0 := by simpa [s] using hi
  have hz : ∀ k, k ≠ i → hP.isHermitian.eigenvalues k = 0 := by
    intro k hki
    by_contra hk
    exact hki ((Finset.card_le_one.mp hs) k (by simp [s, hk]) i hi)
  let u : n → ℂ := hP.isHermitian.eigenvectorBasis i
  have hu : vecNormSq u = 1 := by
    have hgram : ∀ a b, braket
        (fun k => hP.isHermitian.eigenvectorBasis a k)
        (fun k => hP.isHermitian.eigenvectorBasis b k) = if a = b then 1 else 0 := by
      intro a b
      simpa [braket, dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
        Complex.star_def, mul_comm] using hP.isHermitian.eigenvectorBasis.inner_eq_ite a b
    have h := congrArg Complex.re (hgram i i)
    simpa only [u, if_true, braket_self, Complex.ofReal_re, Complex.one_re] using h
  refine ⟨u, hP.isHermitian.eigenvalues i, hu,
    lt_of_le_of_ne (hP.eigenvalues_nonneg i) (Ne.symm hi0), ?_⟩
  ext a b
  rw [hermitian_spectral_entry P hP.isHermitian a b]
  rw [Finset.sum_eq_single i]
  · simp [u, ketBra, Matrix.smul_apply, mul_assoc]
  · intro k _ hki
    simp [hz k hki]
  · simp

end ThreeCopyQutritWerner
