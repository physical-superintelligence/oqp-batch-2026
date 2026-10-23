module

public import ThreeCopyQutritWerner.ThinPencilRankDrop
public import ThreeCopyQutritWerner.JointPencilSupport

@[expose] public section


/-!
# Independent source/corange parameters for the original thin pencil

The literal factors and their conjugate parameter first give both physical
joint minors outside the constructed finite rank-drop set. Polynomial
separation removes that exception and separates the two complex parameters.
No common-plane conclusion is assumed in this step.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

theorem twoSiteJointFactorFlatten_affine
    (A B C D : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ) (z w : ℂ) :
    twoSiteJointFactorFlatten (A + z • B) (C + w • D) =
      jointAffinePencil (twoSiteFactorFlatten A) (twoSiteFactorFlatten B)
        (twoSiteFactorFlatten C) (twoSiteFactorFlatten D) z w := by
  ext i q
  cases q <;> rfl

theorem twoSiteFactorFlatten_neg {a b n : Type*} (A : Matrix (a × b) n ℂ) :
    twoSiteFactorFlatten (-A) = -twoSiteFactorFlatten A := rfl

theorem twoSiteFactorFlip_affine {a b n : Type*}
    (A B : Matrix (a × b) n ℂ) (z : ℂ) :
    twoSiteFactorFlip (A + z • B) = twoSiteFactorFlip A + z • twoSiteFactorFlip B := rfl

theorem twoSiteFactorFlip_neg {a b n : Type*} (A : Matrix (a × b) n ℂ) :
    twoSiteFactorFlip (-A) = -twoSiteFactorFlip A := rfl

/-- Both physical local coefficient families have zero joint minors at
every pair of independent complex parameters, derived from the actual
original endpoint zero and one nonzero cut-pencil member. -/
theorem thinFirstSite_joint_factor_minors_independent
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) (z₀ : ℂ)
    (hne : (firstSiteFactorBlock X 0 + z₀ • firstSiteFactorBlock X 1) *
      (firstSiteFactorBlock Y 1 - conj z₀ • firstSiteFactorBlock Y 0)ᴴ ≠ 0) :
    (∀ z w : ℂ, ∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
      ((jointAffinePencil
        (twoSiteFactorFlatten (firstSiteFactorBlock X 0))
        (twoSiteFactorFlatten (firstSiteFactorBlock X 1))
        (twoSiteFactorFlatten (firstSiteFactorBlock Y 1))
        (-twoSiteFactorFlatten (firstSiteFactorBlock Y 0)) z w).submatrix id cols).det = 0) ∧
    (∀ z w : ℂ, ∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
      ((jointAffinePencil
        (twoSiteFactorFlatten (twoSiteFactorFlip (firstSiteFactorBlock X 0)))
        (twoSiteFactorFlatten (twoSiteFactorFlip (firstSiteFactorBlock X 1)))
        (twoSiteFactorFlatten (twoSiteFactorFlip (firstSiteFactorBlock Y 1)))
        (-twoSiteFactorFlatten (twoSiteFactorFlip (firstSiteFactorBlock Y 0))) z w).submatrix id cols).det = 0) := by
  obtain ⟨s, hs, hp⟩ := thinFirstSite_joint_factor_minors_off_finite X Y hC hz hrow z₀ hne
  constructor
  · intro z w cols
    refine jointAffinePencil_minors_separate_off_countable _ _ _ _ s hs.countable ?_ z w cols
    intro t hts rows
    simpa only [sub_eq_add_neg, ← smul_neg, twoSiteJointFactorFlatten_affine,
      twoSiteFactorFlatten_neg] using (hp t hts).1 rows
  · intro z w cols
    refine jointAffinePencil_minors_separate_off_countable _ _ _ _ s hs.countable ?_ z w cols
    intro t hts rows
    simpa only [sub_eq_add_neg, ← smul_neg, twoSiteFactorFlip_affine,
      twoSiteFactorFlip_neg, twoSiteJointFactorFlatten_affine, twoSiteFactorFlatten_neg]
      using (hp t hts).2 rows

end ThreeCopyQutritWerner
