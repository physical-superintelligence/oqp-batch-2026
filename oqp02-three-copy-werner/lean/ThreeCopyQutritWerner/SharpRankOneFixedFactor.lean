module

public import ThreeCopyQutritWerner.SharpProductGamma

@[expose] public section


/-!
# Literal fixed-factor forms for an all-rank-one family

The proportional factors in the common-factor classification are absorbed
into the varying factors. The fixed vector is an actual nonzero original
factor; no normalization or chosen factorization is supplied by the caller.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Every normalized all-rank-one combination family has one literal fixed
nonzero factor, on one of the two original local registers. -/
theorem sharpRankOneFamily_exists_fixed_factor
    {ι L R : Type*} [Fintype ι] [Fintype L] [Fintype R] [DecidableEq ι]
    (u : ι → L × R → ℂ) (hu : ∀ i, vecNormSq (u i) = 1)
    (hr : ∀ z : ι → ℂ, (sharpReshape (fun r => ∑ i, z i * u i r)).rank ≤ 1)
    (i₀ : ι) :
    (∃ a : L → ℂ, (∃ l, a l ≠ 0) ∧ ∃ y : ι → R → ℂ,
      ∀ i, u i = sharpProductVector a (y i)) ∨
    (∃ b : R → ℂ, (∃ r, b r ≠ 0) ∧ ∃ x : ι → L → ℂ,
      ∀ i, u i = sharpProductVector (x i) b) := by
  classical
  obtain ⟨x, y, he, hx, hy, hfixed⟩ := sharpRankOneFamily_exists_common_factor u hu hr i₀
  rcases hfixed with hleft | hright
  · left
    choose c hc using hleft
    refine ⟨x i₀, hx i₀, fun i r => c i * y i r, ?_⟩
    intro i
    funext ⟨l, r⟩
    rw [he, hc]
    simp only [sharpProductVector]
    ring
  · right
    choose c hc using hright
    refine ⟨y i₀, hy i₀, fun i l => c i * x i l, ?_⟩
    intro i
    funext ⟨l, r⟩
    rw [he, hc]
    simp only [sharpProductVector]
    ring

end ThreeCopyQutritWerner
