module

public import ThreeCopyQutritWerner.TwoCutSingleFactor
public import ThreeCopyQutritWerner.TwoCutFixedSourceTrace
public import ThreeCopyQutritWerner.TwoSiteFactorRanks
public import ThreeCopyQutritWerner.RankTwoProductRanges

@[expose] public section


/-!
# A single-output cut zero also has a single local corange

The actual ket-bra/projection classification is used in the same physical
site. Cancelling a full-rank opposite factor transfers this statement to
the literal local flattening of its partner, without a support premise.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem cutForm_zero_single_output_adjoint
    {d : Type*} [Fintype d] [DecidableEq d]
    (C : Matrix (Fin 3 × d) (Fin 3 × d) ℂ) (hr : C.rank ≤ 2)
    (hq : cutForm C = 0) (h : HasSingleFirstOutput C) : HasSingleFirstOutput Cᴴ := by
  by_cases hz : C = 0
  · refine ⟨0, fun i => if i = 0 then 1 else 0, by simp, ?_⟩
    intro i r q
    simp [hz]
  obtain ⟨i, x, hx, hf⟩ := h
  obtain ⟨u, v, P, _, _, _, _, _, he⟩ :=
    cutForm_zero_single_output_factor C hr hq hz i x hx hf
  rw [he, Matrix.conjTranspose_kronecker, conjTranspose_ketBra]
  exact hasSingleFirstOutput_ketBra_kronecker v u Pᴴ

theorem cutForm_zero_single_factor_partner_local_rank_le_one
    {d : Type*} [Fintype d] [DecidableEq d]
    (Z X : Matrix (Fin 3 × d) (Fin 2) ℂ) (hZ : Z.rank = 2)
    (hq : cutForm (Z * Xᴴ) = 0) (h : HasSingleFirstOutput (Z * Xᴴ)) :
    (twoSiteFactorFlatten X).rank ≤ 1 := by
  have hr : (Z * Xᴴ).rank ≤ 2 :=
    (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width Z)
  have hs := cutForm_zero_single_output_adjoint (Z * Xᴴ) hr hq h
  have hR : LinearMap.range X.mulVecLin ≤ LinearMap.range (Z * Xᴴ)ᴴ.mulVecLin := by
    have he := matrix_range_mul_eq_of_rank_eq X Zᴴ
      (rank_mul_conjTranspose_eq_of_full_two_columns X Z hZ)
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, he] using
      (le_rfl : LinearMap.range X.mulVecLin ≤ LinearMap.range X.mulVecLin)
  exact (twoSiteFactorFlatten_rank_le_of_range_le X (Z * Xᴴ)ᴴ hR).trans
    (twoSiteFactorFlatten_rank_le_one_of_single_output _ hs)

end ThreeCopyQutritWerner
