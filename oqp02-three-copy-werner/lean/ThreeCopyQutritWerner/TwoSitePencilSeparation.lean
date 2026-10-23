module

public import ThreeCopyQutritWerner.ThinPencilJointSeparation

@[expose] public section


/-!
# Joint local minors of actual cut-zero factor pencils

This reusable step accepts actual cut zeros, constructs finite rank-drop
exceptions from one nonzero member, and separates both physical local minor
families. No common plane or generic full-rank hypothesis is supplied.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

theorem twoSite_cut_zero_pencil_joint_minors_independent
    (A B C D : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ)
    (hq : ∀ z : ℂ, cutForm ((A + z • B) * (C + conj z • D)ᴴ) = 0)
    (z₀ : ℂ) (hne : (A + z₀ • B) * (C + conj z₀ • D)ᴴ ≠ 0) :
    (∀ z w : ℂ, ∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
      ((twoSiteJointFactorFlatten (A + z • B) (C + w • D)).submatrix id cols).det = 0) ∧
    (∀ z w : ℂ, ∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
      ((twoSiteJointFactorFlatten (twoSiteFactorFlip (A + z • B))
        (twoSiteFactorFlip (C + w • D))).submatrix id cols).det = 0) := by
  have hr : ((A + z₀ • B) * (C + conj z₀ • D)ᴴ).rank ≤ 2 :=
    (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width (A + z₀ • B))
  have ht := rank_two_of_nonzero_cutForm_zero _ hr (hq z₀) hne
  obtain ⟨hX, hYH⟩ := rank_eq_two_of_mul (A + z₀ • B) (C + conj z₀ • D)ᴴ ht
  have hY : (C + conj z₀ • D).rank = 2 := by
    simpa only [Matrix.rank_conjTranspose] using hYH
  obtain ⟨sX, hsX, hrX⟩ := affinePencil_rank_two_off_finite A B
    (fun z => by simpa using Matrix.rank_le_card_width (A + z • B)) z₀ hX
  obtain ⟨sY, hsY, hrY⟩ := affinePencil_rank_two_off_finite C D
    (fun w => by simpa using Matrix.rank_le_card_width (C + w • D)) (conj z₀) hY
  let s := sX ∪ conj '' sY
  have hs : s.Finite := hsX.union (hsY.image conj)
  have hp (z : ℂ) (hz : z ∉ s) :
      (∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
        ((twoSiteJointFactorFlatten (A + z • B) (C + conj z • D)).submatrix id cols).det = 0) ∧
      (∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
        ((twoSiteJointFactorFlatten (twoSiteFactorFlip (A + z • B))
          (twoSiteFactorFlip (C + conj z • D))).submatrix id cols).det = 0) := by
    have hx : z ∉ sX := fun h => hz (Or.inl h)
    have hy : conj z ∉ sY := by
      intro h
      exact hz (Or.inr ⟨conj z, h, by simp⟩)
    exact twoSiteJointFactorFlatten_both_minors_zero _ _ (hrX z hx) (hrY (conj z) hy) (hq z)
  constructor
  · intro z w cols
    rw [twoSiteJointFactorFlatten_affine]
    refine jointAffinePencil_minors_separate_off_countable _ _ _ _ s hs.countable ?_ z w cols
    intro t ht rows
    simpa only [twoSiteJointFactorFlatten_affine] using (hp t ht).1 rows
  · intro z w cols
    rw [twoSiteFactorFlip_affine, twoSiteFactorFlip_affine, twoSiteJointFactorFlatten_affine]
    refine jointAffinePencil_minors_separate_off_countable _ _ _ _ s hs.countable ?_ z w cols
    intro t ht rows
    simpa only [twoSiteFactorFlip_affine, twoSiteJointFactorFlatten_affine] using (hp t ht).2 rows

end ThreeCopyQutritWerner
