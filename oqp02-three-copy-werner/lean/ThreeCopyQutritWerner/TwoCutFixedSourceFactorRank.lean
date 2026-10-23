module

public import ThreeCopyQutritWerner.TwoCutSingleFactorRank
public import ThreeCopyQutritWerner.TwoSiteJointFactorFlip
public import ThreeCopyQutritWerner.TwoCutNonzeroRank

@[expose] public section


/-!
# The local factor exceptions of a fixed-source cut-zero family

A single-output anchor transfers its literal source factor to every family
member. Cut-zero rigidity then bounds the partner's local rank at the same
physical site. The partner directions may vary with the family index.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem twoCut_fixed_source_single_factor_partner_ranks
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (Z : Matrix (Fin 3 × d) (Fin 2) ℂ) (X : ι → Matrix (Fin 3 × d) (Fin 2) ℂ)
    (hZ : Z.rank = 2) (hq : ∀ i, cutForm (Z * (X i)ᴴ) = 0) (i₀ : ι)
    (hne : Z * (X i₀)ᴴ ≠ 0) (hfirst : HasSingleFirstOutput (Z * (X i₀)ᴴ)) :
    ∀ i, (twoSiteFactorFlatten (X i)).rank ≤ 1 := by
  have hr : (Z * (X i₀)ᴴ).rank ≤ 2 :=
    (Matrix.rank_mul_le_left _ _).trans hZ.le
  have hr₀ := rank_two_of_nonzero_cutForm_zero _ hr (hq i₀) hne
  have hR₀ : LinearMap.range (Z * (X i₀)ᴴ).mulVecLin = LinearMap.range Z.mulVecLin :=
    matrix_range_mul_eq_of_rank_eq Z (X i₀)ᴴ (hr₀.trans hZ.symm)
  intro i
  have hR : LinearMap.range (Z * (X i)ᴴ).mulVecLin ≤
      LinearMap.range (Z * (X i₀)ᴴ).mulVecLin := by
    rw [hR₀]
    rintro _ ⟨v, rfl⟩
    refine ⟨(X i)ᴴ *ᵥ v, ?_⟩
    change Z *ᵥ ((X i)ᴴ *ᵥ v) = (Z * (X i)ᴴ) *ᵥ v
    exact Matrix.mulVec_mulVec v Z (X i)ᴴ
  exact cutForm_zero_single_factor_partner_local_rank_le_one Z (X i) hZ (hq i)
    (hasSingleFirstOutput_of_range_le _ _ hR hfirst)

theorem twoCut_fixed_source_second_factor_partner_ranks
    {ι : Type*}
    (Z : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ)
    (X : ι → Matrix (Fin 3 × Fin 3) (Fin 2) ℂ)
    (hZ : Z.rank = 2) (hq : ∀ i, cutForm (Z * (X i)ᴴ) = 0) (i₀ : ι)
    (hne : Z * (X i₀)ᴴ ≠ 0) (hsecond : HasSingleFirstOutput (twoCutSwap (Z * (X i₀)ᴴ))) :
    ∀ i, (twoSiteFactorFlatten (twoSiteFactorFlip (X i))).rank ≤ 1 := by
  refine twoCut_fixed_source_single_factor_partner_ranks (twoSiteFactorFlip Z)
    (fun i => twoSiteFactorFlip (X i)) ((twoSiteFactorFlip_rank Z).trans hZ) ?_ i₀ ?_ ?_
  · intro i
    rw [twoSiteFactorFlip_product, (twoCutSwap_data (Z * (X i)ᴴ)).2.2]
    exact hq i
  · intro he
    apply hne
    rw [twoSiteFactorFlip_product] at he
    calc
      Z * (X i₀)ᴴ = twoCutSwap (twoCutSwap (Z * (X i₀)ᴴ)) := rfl
      _ = twoCutSwap 0 := congrArg twoCutSwap he
      _ = 0 := rfl
  · simpa only [twoSiteFactorFlip_product] using hsecond

end ThreeCopyQutritWerner
