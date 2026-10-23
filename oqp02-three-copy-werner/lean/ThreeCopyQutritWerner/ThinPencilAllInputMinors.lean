module

public import ThreeCopyQutritWerner.ThinPencilFreeInput
public import ThreeCopyQutritWerner.TwoSiteFreePencilSeparation

@[expose] public section


/-!
# All original input coefficients in the separated physical local minors

The anchor may occur at any free-input parameter. Translation of that
parameter brings it to the generic separation theorem without discarding
the third input block or postulating an unperturbed nonzero pencil.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

theorem thinFirstSite_all_input_joint_minors_independent
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) (z₀ t₀ : ℂ)
    (hne : (firstSiteFactorBlock X 0 + z₀ • firstSiteFactorBlock X 1) *
      (firstSiteFactorBlock Y 1 - conj z₀ • firstSiteFactorBlock Y 0 +
        t₀ • firstSiteFactorBlock Y 2)ᴴ ≠ 0) :
    ∀ z w t : ℂ,
      let A := firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1
      let B := firstSiteFactorBlock Y 1 - w • firstSiteFactorBlock Y 0 +
        t • firstSiteFactorBlock Y 2
      (∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
        ((twoSiteJointFactorFlatten A B).submatrix id cols).det = 0) ∧
      (∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
        ((twoSiteJointFactorFlatten (twoSiteFactorFlip A)
          (twoSiteFactorFlip B)).submatrix id cols).det = 0) := by
  let A := firstSiteFactorBlock X 0
  let B := firstSiteFactorBlock X 1
  let C := firstSiteFactorBlock Y 1
  let D := firstSiteFactorBlock Y 0
  let E := firstSiteFactorBlock Y 2
  have hq (z t : ℂ) : cutForm ((A + z • B) *
      ((C + t₀ • E) + conj z • (-D) + t • E)ᴴ) = 0 := by
    have he : (C + t₀ • E) + conj z • (-D) + t • E =
        C - conj z • D + (t₀ + t) • E := by
      simp only [smul_neg, add_smul]
      abel
    rw [he]
    exact (thinFirstSite_free_input_factor_rank_cut_zero X Y hC hz hrow z (t₀ + t)).2
  have hn : (A + z₀ • B) * ((C + t₀ • E) + conj z₀ • (-D))ᴴ ≠ 0 := by
    have he : (C + t₀ • E) + conj z₀ • (-D) = C - conj z₀ • D + t₀ • E := by
      simp only [smul_neg]
      abel
    rw [he]
    exact hne
  obtain ⟨hp, hp'⟩ := twoSite_cut_zero_free_pencil_joint_minors_independent
    A B (C + t₀ • E) (-D) E hq z₀ hn
  intro z w t
  have he : (C + t₀ • E) + w • (-D) + (t - t₀) • E = C - w • D + t • E := by
    simp only [smul_neg, sub_smul]
    abel
  constructor
  · intro cols
    simpa only [he] using hp z w (t - t₀) cols
  · intro cols
    simpa only [he] using hp' z w (t - t₀) cols

/-- Both retained sites obey the literal joint local rank bound for all
independent source, corange and off-plane input coefficients. -/
theorem thinFirstSite_all_input_joint_rank_le_two
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) (z₀ t₀ : ℂ)
    (hne : (firstSiteFactorBlock X 0 + z₀ • firstSiteFactorBlock X 1) *
      (firstSiteFactorBlock Y 1 - conj z₀ • firstSiteFactorBlock Y 0 +
        t₀ • firstSiteFactorBlock Y 2)ᴴ ≠ 0) (z w t : ℂ) :
    let A := firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1
    let B := firstSiteFactorBlock Y 1 - w • firstSiteFactorBlock Y 0 +
      t • firstSiteFactorBlock Y 2
    (twoSiteJointFactorFlatten A B).rank ≤ 2 ∧
      (twoSiteJointFactorFlatten (twoSiteFactorFlip A) (twoSiteFactorFlip B)).rank ≤ 2 := by
  obtain ⟨hp, hp'⟩ := thinFirstSite_all_input_joint_minors_independent X Y hC hz hrow z₀ t₀ hne z w t
  exact ⟨rank_le_two_of_all_three_minors_zero _ hp,
    rank_le_two_of_all_three_minors_zero _ hp'⟩

end ThreeCopyQutritWerner
