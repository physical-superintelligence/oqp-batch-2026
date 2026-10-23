module

public import ThreeCopyQutritWerner.ZeroRelationsSpan
public import ThreeCopyQutritWerner.ZeroRelationsRankOne
public import ThreeCopyQutritWerner.ZeroRelationsLocalSpan

@[expose] public section


/-!
# Appendix C: assembly of the thin-source reduction

The zero relations, together with the two explicitly assumed analytic inputs, imply that
the source of a rank-two endpoint zero is thin at some site. The proof splits on the rank
of the symmetric feature `H`: rank zero uses `AppCInput1`, rank one produces a product ray
and uses `AppCInput2`, and rank two uses the proved local-plane algebra.

For arbitrary normalized endpoint zeros, membership of their features in the span of the
known zero families is a separate explicit premise. This is the still-open certificate
kernel implication, not a conclusion of the known-family direction. The final classification
also requires the separate, explicitly assumed `AppCInput3`.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

private theorem matrix_eq_zero_of_rank_eq_zero {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) (hr : M.rank = 0) : M = 0 := by
  obtain ⟨U, V, hUV⟩ := (rank_le_iff_exists_mul M 0).mp hr.le
  rw [hUV]
  ext i j
  simp [Matrix.mul_apply]

/-- Appendix C's rank split, with both analytic equality inputs retained as hypotheses.
The zero relations themselves are also an explicit hypothesis. -/
theorem hasThinLocalRange_of_zeroRelations
    (hApp1 : AppCInput1) (hApp2 : AppCInput2)
    (X : Matrix QutritSites (Fin 2) ℂ) (B : Matrix (Fin 2) QutritSites ℂ)
    (hr : (X * B).rank = 2) (hq : endpointEnergy (X * B) = 0)
    (hrel : ZeroRelations (hFeature (X * B) (bivecMat X)) (bivecMat X)) :
    HasThinLocalRange (X * B) := by
  by_contra hthin
  have hn1 : ¬ localRangeDim₁ (X * B) ≤ 2 := fun h => hthin (Or.inl h)
  have hn2 : ¬ localRangeDim₂ (X * B) ≤ 2 := fun h => hthin (Or.inr (Or.inl h))
  have hn3 : ¬ localRangeDim₃ (X * B) ≤ 2 := fun h => hthin (Or.inr (Or.inr h))
  obtain ⟨hp1, hp2, hp3⟩ := siteAnti_bivec_ne_zero_of_localRangeDim_gt_one X B hr
    (by omega) (by omega) (by omega)
  obtain ⟨h1, h2, _⟩ := local_symmetry_of_zeroRelations (X * B) (bivecMat X)
    (bivecMat_transpose X) hrel hp1 hp2 hp3
  have hHle := rank_hFeature_le X B
  have hcases : (hFeature (X * B) (bivecMat X)).rank = 0 ∨
      (hFeature (X * B) (bivecMat X)).rank = 1 ∨
      (hFeature (X * B) (bivecMat X)).rank = 2 := by omega
  rcases hcases with hH0 | hH1 | hH2
  · have hzero := matrix_eq_zero_of_rank_eq_zero _ hH0
    have hsq := mul_self_eq_trace_smul_of_hFeature_eq_zero X B hr hzero
    have hlocal := (hApp1 (X * B) ((X * B).trace / 2) hr hsq).2 hq
    rcases hlocal with ht | ht | ht
    · exact hn1 ht.1
    · exact hn2 ht.1
    · exact hn3 ht.1
  · have hprod := exists_product_in_range_of_hFeature_rank_one X B hr hH1 h1 h2
    exact hn1 (hApp2 (X * B) hr hq hprod).1
  · exact hn1 (localRangeDim₁_le_two_of_hFeature_rank_two X B hH2 h1)

/-- REDUCTION: arbitrary-zero membership in the known-feature span and the two analytic
Appendix C inputs imply the thin-source property. No kernel-completeness claim is hidden
in the statement: membership is required explicitly for every normalized endpoint-zero
rank-two factorization. -/
theorem thinSourceProperty_of_knownZeroFeatureSpan
    (hApp1 : AppCInput1) (hApp2 : AppCInput2)
    (hspan : ∀ (X : Matrix QutritSites (Fin 2) ℂ) (B : Matrix (Fin 2) QutritSites ℂ),
      (X * B).rank = 2 → invN (X * B) = 1 → endpointEnergy (X * B) = 0 →
        featureH (X * B) (bivecMat X) ∈ knownZeroFeatureSpan) :
    ThinSourceProperty := by
  intro C hr hN hq
  have hC : C ≠ 0 := by
    intro hzero
    simpa [hzero, invN, frobSq] using hN
  have hr2 := rank_eq_two_of_endpointEnergy_eq_zero C hr hq hC
  obtain ⟨X, B, rfl⟩ := (rank_le_iff_exists_mul C 2).mp hr
  exact hasThinLocalRange_of_zeroRelations hApp1 hApp2 X B hr2 hq
    (zeroRelations_of_mem_knownZeroFeatureSpan (X * B) X (hspan X B hr2 hN hq))

/-- REDUCTION: the explicit saturated-kernel implication and all three Appendix C analytic
inputs suffice for the classification. This theorem does not discharge any of those four
remaining manuscript dependencies. -/
theorem qutritZeroClassification_of_knownZeroFeatureSpan
    (hApp1 : AppCInput1) (hApp2 : AppCInput2) (hApp3 : AppCInput3)
    (hspan : ∀ (X : Matrix QutritSites (Fin 2) ℂ) (B : Matrix (Fin 2) QutritSites ℂ),
      (X * B).rank = 2 → invN (X * B) = 1 → endpointEnergy (X * B) = 0 →
        featureH (X * B) (bivecMat X) ∈ knownZeroFeatureSpan) :
    QutritZeroClassification :=
  qutritZeroClassification_of_thinSource
    (thinSourceProperty_of_knownZeroFeatureSpan hApp1 hApp2 hspan) hApp3

end ThreeCopyQutritWerner

end
