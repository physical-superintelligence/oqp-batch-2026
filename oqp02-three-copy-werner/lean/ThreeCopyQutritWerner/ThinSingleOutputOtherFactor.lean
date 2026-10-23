module

public import ThreeCopyQutritWerner.ThinSingleOutputOtherTransport
public import ThreeCopyQutritWerner.ThinSingleOutputFactorBranch
public import ThreeCopyQutritWerner.ThinFirstThirdFamilyI

@[expose] public section


/-! The opposite anchor-factor orientation in the original three-site operator. -/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem isQutritZeroFamilyMember_of_single_output_anchor_other_factor
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1) (k j₀ : Fin 3)
    (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0)
    (hne : firstSiteBlock C k j₀ ≠ 0)
    (hfactor : HasSingleFirstOutput (twoCutSwap (firstSiteBlock C k j₀))) :
    IsQutritZeroFamilyMember C := by
  obtain ⟨i₀, x, hx, hf⟩ := hfactor
  obtain ⟨V, hV, hArow⟩ := twoCut_single_output_exists_unitary_coordinate
    (twoCutSwap (firstSiteBlock C k j₀)) i₀ x hx hf
  let I₃ : Matrix (Fin 3) (Fin 3) ℂ := 1
  have hI : I₃ᴴ * I₃ = 1 := by simp [I₃]
  let D := embed₃ I₃ I₃ V C
  have hDr : D.rank ≤ 2 := (productRay_rank_embed₃ hI hI hV C).trans_le hC
  have hDz : endpointEnergy D = 0 := (productRay_endpointEnergy_embed₃ hI hI hV C).trans hz
  have hDN : frobSq D = 1 := (frobSq_embed₃ hI hI hV C).trans hN
  have hDrow : ∀ i, i ≠ k → ∀ r q, D (i, r) q = 0 := by
    dsimp [D, I₃]
    rw [embed₃_eq_mul]
    exact first_output_coordinate_conj_remaining C (1 ⊗ₖ V) k hrow
  have hblock : firstSiteBlock D k j₀ =
      (I₃ ⊗ₖ V) * firstSiteBlock C k j₀ * (I₃ ⊗ₖ V)ᴴ := by
    dsimp [D, I₃]
    rw [embed₃_eq_mul, firstSiteBlock_conj_remaining]
  have hDne : firstSiteBlock D k j₀ ≠ 0 := by
    intro he
    have hrec := twoCut_unitary_conj_recover (I₃ ⊗ₖ V) (firstSiteBlock C k j₀)
      (kron_isometry I₃ V hI hV)
    rw [← hblock, he, Matrix.mul_zero, Matrix.zero_mul] at hrec
    exact hne hrec.symm
  have hswap : twoCutSwap (firstSiteBlock D k j₀) =
      (V ⊗ₖ I₃) * twoCutSwap (firstSiteBlock C k j₀) * (V ⊗ₖ I₃)ᴴ := by
    rw [hblock, twoCutSwap_local_conj]
  have hDanchor (r : Fin 3) (hr : r ≠ 0) (j : Fin 3) (q : Fin 3 × Fin 3) :
      firstSiteBlock D k j₀ (j, r) q = 0 := by
    have he := hArow r hr j (q.2, q.1)
    rw [← hswap] at he
    exact he
  have hDthird : ∀ r, r ≠ 0 → ∀ i j q, D (i, j, r) q = 0 := by
    intro r hr i j q
    exact single_output_anchor_zero_row_propagates D hDr hDz k j₀ hDrow hDne
      (j, r) (hDanchor r hr j) i q
  have hmember := isQutritZeroFamilyMember_of_first_third_output_coordinates D hDr hDz hDN
    k 0 hDrow hDthird
  exact (isQutritZeroFamilyMember_local_unitary_iff I₃ I₃ V hI hI hV C).mp hmember

end ThreeCopyQutritWerner
