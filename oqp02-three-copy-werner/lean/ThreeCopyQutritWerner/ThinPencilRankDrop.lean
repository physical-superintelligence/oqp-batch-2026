module

public import ThreeCopyQutritWerner.ThinPencilFactors
public import ThreeCopyQutritWerner.TwoSiteJointFactorFlip
public import ThreeCopyQutritWerner.AffinePencilRankDrop
public import ThreeCopyQutritWerner.TwoCutNonzeroRank

@[expose] public section


/-!
# Finite exceptional parameters for an actual nonzero thin cut pencil

A nonzero cut-zero pencil member has rank two, so both of its actual
two-column factors have rank two. The two affine rank-drop sets are finite;
the corange set is transported through actual complex conjugation.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

theorem thinFirstSite_factor_rank_two_off_finite
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) (z₀ : ℂ)
    (hne : (firstSiteFactorBlock X 0 + z₀ • firstSiteFactorBlock X 1) *
      (firstSiteFactorBlock Y 1 - conj z₀ • firstSiteFactorBlock Y 0)ᴴ ≠ 0) :
    ∃ s : Set ℂ, s.Finite ∧ ∀ z ∉ s,
      (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1).rank = 2 ∧
      (firstSiteFactorBlock Y 1 - conj z • firstSiteFactorBlock Y 0).rank = 2 := by
  obtain ⟨hr, hq⟩ := thinFirstSite_affine_factor_rank_cut_zero X Y hC hz hrow z₀
  have ht := rank_two_of_nonzero_cutForm_zero _ hr hq hne
  obtain ⟨hX, hYH⟩ := rank_eq_two_of_mul
    (firstSiteFactorBlock X 0 + z₀ • firstSiteFactorBlock X 1)
    (firstSiteFactorBlock Y 1 - conj z₀ • firstSiteFactorBlock Y 0)ᴴ ht
  have hY : (firstSiteFactorBlock Y 1 + conj z₀ • (-firstSiteFactorBlock Y 0)).rank = 2 := by
    simpa only [Matrix.rank_conjTranspose, smul_neg, ← sub_eq_add_neg] using hYH
  obtain ⟨sX, hsX, hrX⟩ := affinePencil_rank_two_off_finite
    (firstSiteFactorBlock X 0) (firstSiteFactorBlock X 1)
    (fun z => by simpa using (Matrix.rank_le_card_width
      (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1))) z₀ hX
  obtain ⟨sY, hsY, hrY⟩ := affinePencil_rank_two_off_finite
    (firstSiteFactorBlock Y 1) (-firstSiteFactorBlock Y 0)
    (fun w => by simpa using (Matrix.rank_le_card_width
      (firstSiteFactorBlock Y 1 + w • (-firstSiteFactorBlock Y 0)))) (conj z₀) hY
  refine ⟨sX ∪ conj '' sY, hsX.union (hsY.image conj), ?_⟩
  intro z hzs
  have hx : z ∉ sX := fun h => hzs (Or.inl h)
  have hy : conj z ∉ sY := by
    intro h
    exact hzs (Or.inr ⟨conj z, h, by simp⟩)
  refine ⟨hrX z hx, ?_⟩
  simpa only [smul_neg, ← sub_eq_add_neg] using hrY (conj z) hy

/-- Both faithful physical local joint-minor families vanish away from
one constructed finite exceptional set, using the original zero alone and
one actual nonzero pencil member. -/
theorem thinFirstSite_joint_factor_minors_off_finite
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) (z₀ : ℂ)
    (hne : (firstSiteFactorBlock X 0 + z₀ • firstSiteFactorBlock X 1) *
      (firstSiteFactorBlock Y 1 - conj z₀ • firstSiteFactorBlock Y 0)ᴴ ≠ 0) :
    ∃ s : Set ℂ, s.Finite ∧ ∀ z ∉ s,
      let A := firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1
      let B := firstSiteFactorBlock Y 1 - conj z • firstSiteFactorBlock Y 0
      (∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
        ((twoSiteJointFactorFlatten A B).submatrix id cols).det = 0) ∧
      (∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
        ((twoSiteJointFactorFlatten (twoSiteFactorFlip A)
          (twoSiteFactorFlip B)).submatrix id cols).det = 0) := by
  obtain ⟨s, hs, hr⟩ := thinFirstSite_factor_rank_two_off_finite X Y hC hz hrow z₀ hne
  refine ⟨s, hs, ?_⟩
  intro z hzs
  have hq := (thinFirstSite_affine_factor_rank_cut_zero X Y hC hz hrow z).2
  exact twoSiteJointFactorFlatten_both_minors_zero _ _ (hr z hzs).1 (hr z hzs).2 hq

end ThreeCopyQutritWerner
