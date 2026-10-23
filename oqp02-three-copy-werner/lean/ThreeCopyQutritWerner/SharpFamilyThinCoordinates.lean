module

public import ThreeCopyQutritWerner.SharpGammaFamilyClassification
public import ThreeCopyQutritWerner.SharpFixedPairAnnihilator

@[expose] public section


/-!
# One physical thin register for both sharp singular families

The two fixed vectors in each product-family alternative admit one common
unitary annihilator. Thus all three exhaustive alternatives produce a literal
missing coordinate on one of the original physical registers.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- The common-support alternatives construct an actual missing coordinate
on a common physical register of both entire original families. -/
theorem sharpQutritFamilyCommonSupport_exists_annihilator
    {ι : Type*} (u v : ι → Fin 3 × Fin 3 → ℂ)
    (h : SharpQutritFamilyCommonSupport u v) :
    (∃ U : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3, Uᴴ * U = 1 ∧
      ∀ k c, (U * sharpReshape (u k)) a c = 0 ∧ (U * sharpReshape (v k)) a c = 0) ∨
    (∃ U : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3, Uᴴ * U = 1 ∧
      ∀ k c, (U * (sharpReshape (u k))ᵀ) a c = 0 ∧
        (U * (sharpReshape (v k))ᵀ) a c = 0) := by
  rcases h with h | ⟨a, b, ha, hb, y, z, he⟩ | ⟨a, b, ha, hb, x, z, he⟩
  · exact Or.inl h
  · obtain ⟨U, i, hU, hUa, hUb⟩ := sharpFixedPair_exists_unitary_annihilator a b
    refine Or.inl ⟨U, i, hU, ?_⟩
    intro k c
    constructor
    · rw [(he k).1]
      change (∑ r, U i r * (a r * y k c)) = 0
      simpa only [← mul_assoc, ← Finset.sum_mul, hUa, zero_mul]
    · rw [(he k).2]
      change (∑ r, U i r * (b r * z k c)) = 0
      simpa only [← mul_assoc, ← Finset.sum_mul, hUb, zero_mul]
  · obtain ⟨U, i, hU, hUa, hUb⟩ := sharpFixedPair_exists_unitary_annihilator a b
    refine Or.inr ⟨U, i, hU, ?_⟩
    intro k c
    constructor
    · rw [(he k).1]
      change (∑ r, U i r * (x k c * a r)) = 0
      calc
        _ = (∑ r, U i r * a r) * x k c := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r _
          ring
        _ = 0 := by rw [hUa, zero_mul]
    · rw [(he k).2]
      change (∑ r, U i r * (z k c * b r)) = 0
      calc
        _ = (∑ r, U i r * b r) * z k c := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r _
          ring
        _ = 0 := by rw [hUb, zero_mul]

end ThreeCopyQutritWerner
