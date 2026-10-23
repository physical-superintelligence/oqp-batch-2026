module

public import ThreeCopyQutritWerner.HermitianPositiveSplit
public import ThreeCopyQutritWerner.TwoCutRotate
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Fintype.Card

@[expose] public section


/-!
# Actual two-ray decomposition of a positive matrix of rank at most two

The nonzero spectral indices are counted by the matrix rank. Enlarge them to
two distinct spectral indices; zero weights cover rank zero and rank one.
Only the faithful ambient-dimension condition `2 ≤ card n` is needed.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

/-- A Hermitian matrix is the sum of its actual spectral rank-one terms. -/
theorem hermitian_spectral_entry {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hP : P.IsHermitian) (i j : n) :
    P i j = ∑ k, (hP.eigenvalues k : ℂ) * hP.eigenvectorBasis k i *
      conj (hP.eigenvectorBasis k j) := by
  have h := hermitian_cfc_entry P hP id i j
  rw [cfc_id ℝ P hP.isSelfAdjoint] at h
  exact h

/-- A positive rank-at-most-two matrix has an actual orthonormal two-ray
decomposition, with nonnegative weights and all smaller ranks included. -/
theorem posSemidef_rank_le_two_exists_rays {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hP : P.PosSemidef) (hr : P.rank ≤ 2)
    (hn : 2 ≤ Fintype.card n) :
    ∃ (u v : n → ℂ) (lam mu : ℝ),
      vecNormSq u = 1 ∧ vecNormSq v = 1 ∧ braket u v = 0 ∧
      0 ≤ lam ∧ 0 ≤ mu ∧ P = (lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v := by
  classical
  let s := Finset.univ.filter (fun k => hP.isHermitian.eigenvalues k ≠ 0)
  have hs : s.card ≤ 2 := by
    have he : s.card = P.rank := by
      rw [hP.isHermitian.rank_eq_card_non_zero_eigs]
      simp [s, Fintype.card_subtype]
    exact he.trans_le hr
  obtain ⟨t, hst, ht⟩ := Finset.exists_superset_card_eq hs hn
  obtain ⟨i, j, hij, htij⟩ := Finset.card_eq_two.mp ht
  let u : n → ℂ := hP.isHermitian.eigenvectorBasis i
  let v : n → ℂ := hP.isHermitian.eigenvectorBasis j
  have hgram : ∀ a b, braket
      (fun k => hP.isHermitian.eigenvectorBasis a k)
      (fun k => hP.isHermitian.eigenvectorBasis b k) = if a = b then 1 else 0 := by
    intro a b
    simpa [braket, dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      Complex.star_def, mul_comm] using hP.isHermitian.eigenvectorBasis.inner_eq_ite a b
  have hu : vecNormSq u = 1 := by
    have h := congrArg Complex.re (hgram i i)
    simpa only [u, if_true, braket_self, Complex.ofReal_re, Complex.one_re] using h
  have hv : vecNormSq v = 1 := by
    have h := congrArg Complex.re (hgram j j)
    simpa only [v, if_true, braket_self, Complex.ofReal_re, Complex.one_re] using h
  refine ⟨u, v, hP.isHermitian.eigenvalues i, hP.isHermitian.eigenvalues j,
    hu, hv, ?_, hP.eigenvalues_nonneg i, hP.eigenvalues_nonneg j, ?_⟩
  · simpa only [u, v, if_neg hij] using hgram i j
  · ext a b
    rw [hermitian_spectral_entry P hP.isHermitian a b]
    have hz : ∀ k ∉ t, hP.isHermitian.eigenvalues k = 0 := by
      intro k hk
      by_contra hne
      exact hk (hst (by simp [s, hne]))
    calc
      _ = ∑ k ∈ t, (hP.isHermitian.eigenvalues k : ℂ) *
          hP.isHermitian.eigenvectorBasis k a * conj (hP.isHermitian.eigenvectorBasis k b) := by
        symm
        apply Finset.sum_subset t.subset_univ
        intro k _ hk
        simp [hz k hk]
      _ = _ := by simp [htij, hij, u, v, ketBra, Matrix.smul_apply, mul_assoc]

end ThreeCopyQutritWerner
