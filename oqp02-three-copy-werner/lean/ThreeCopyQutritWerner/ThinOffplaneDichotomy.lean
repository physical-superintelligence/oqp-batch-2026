module

public import ThreeCopyQutritWerner.TwoCutFixedSourceDichotomy
public import ThreeCopyQutritWerner.ThinPencilOffplane
public import ThreeCopyQutritWerner.FirstSiteFactorLine

@[expose] public section


/-!
# Exhaustive original-coordinate reduction of a nonzero off-plane factor

The anchor is constructed by cancelling the full original source. The
fixed-source dichotomy then gives an actual original output ray or one of
the two pointwise rank-one local source pencils. No anchor coordinates,
generic-rank claim, or common-plane hypothesis is supplied.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem firstSiteFactorBlock_exists_nonzero_left_product
    {a d : Type*} [Fintype a] [Fintype d]
    (X : Matrix (a × d) (Fin 2) ℂ) (Z : Matrix d (Fin 2) ℂ)
    (hX : X.rank = 2) (hne : Z ≠ 0) :
    ∃ i : a, Z * (firstSiteFactorBlock X i)ᴴ ≠ 0 := by
  by_contra h
  push_neg at h
  have hp : Z * Xᴴ = 0 := by
    ext r ⟨i, s⟩
    exact congrFun (congrFun (h i) r) s
  have hXH : Xᴴ.rank = 2 := by rw [Matrix.rank_conjTranspose, hX]
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_eq_two Xᴴ hXH
  apply hne
  calc
    Z = Z * (Xᴴ * R) := by rw [hR, Matrix.mul_one]
    _ = (Z * Xᴴ) * R := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hp, Matrix.zero_mul]

theorem thinFirstSite_nonzero_offplane_source_dichotomy
    (X Y : Matrix QutritSites (Fin 2) ℂ) (hX : X.rank = 2)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) (hne : firstSiteFactorBlock Y 2 ≠ 0) :
    HasSingleFirstOutput (X * Yᴴ) ∨
      (∀ z : ℂ, (twoSiteFactorFlatten
        (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1)).rank ≤ 1) ∨
      (∀ z : ℂ, (twoSiteFactorFlatten (twoSiteFactorFlip
        (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1))).rank ≤ 1) := by
  let Z := firstSiteFactorBlock Y 2
  let F : Fin 3 ⊕ ℂ → Matrix (Fin 3 × Fin 3) (Fin 2) ℂ :=
    Sum.elim (firstSiteFactorBlock X)
      (fun z => firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1)
  have hZ : Z.rank = 2 :=
    thinFirstSite_offplane_factor_rank_two_of_nonzero X Y hX hC hz hrow hne
  obtain ⟨k, hk⟩ := firstSiteFactorBlock_exists_nonzero_left_product X Z hX hne
  have hq (i : Fin 3 ⊕ ℂ) : cutForm (Z * (F i)ᴴ) = 0 := by
    cases i with
    | inl j =>
        have he : Z * (F (Sum.inl j))ᴴ = (firstSiteBlock (X * Yᴴ) j 2)ᴴ := by
          simp only [Z, F, Sum.elim_inl, firstSiteBlock_mul_conjTranspose,
            Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        rw [he, cutForm_conjTranspose]
        exact firstSiteBlock_cutForm_zero_of_thin_endpoint_zero (X * Yᴴ) hC hz 2 hrow j
    | inr z =>
        have he : Z * (F (Sum.inr z))ᴴ =
            ((firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1) * Zᴴ)ᴴ := by
          simp only [F, Sum.elim_inr, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
        rw [he, cutForm_conjTranspose]
        exact (thinFirstSite_offplane_factor_rank_cut_zero X Y hC hz hrow z).2
  rcases twoCut_fixed_source_partner_dichotomy Z F hZ hq (Sum.inl k) hk with
    hline | hfirst | hsecond
  · left
    apply firstSiteFactor_blocks_line_single_output X Y k
    intro i
    exact hline (Sum.inl i)
  · exact Or.inr (Or.inl (fun z => hfirst (Sum.inr z)))
  · exact Or.inr (Or.inr (fun z => hsecond (Sum.inr z)))

end ThreeCopyQutritWerner
