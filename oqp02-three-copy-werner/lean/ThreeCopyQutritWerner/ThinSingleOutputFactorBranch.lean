module

public import ThreeCopyQutritWerner.ThinSingleOutputTransport
public import ThreeCopyQutritWerner.ThinDoubleOutputFamilyI
public import ThreeCopyQutritWerner.QutritFamilyUnitaryInvariant
public import ThreeCopyQutritWerner.TwoCutFixedSourceCoordinates

@[expose] public section


/-!
# An actual anchor factor gives the original family-I branch

The anchor's one-dimensional second-site output is moved to a coordinate
by a constructed unitary. Its actual common source propagates that coordinate
to the whole original operator. Classification is then pulled back by the
proved local-unitary invariance of the exact family union.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem isQutritZeroFamilyMember_of_single_output_anchor_factor
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1) (k j₀ : Fin 3)
    (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0)
    (hne : firstSiteBlock C k j₀ ≠ 0)
    (hfactor : HasSingleFirstOutput (firstSiteBlock C k j₀)) :
    IsQutritZeroFamilyMember C := by
  obtain ⟨i₀, x, hx, hf⟩ := hfactor
  obtain ⟨U, hU, hArow⟩ := twoCut_single_output_exists_unitary_coordinate
    (firstSiteBlock C k j₀) i₀ x hx hf
  let I₃ : Matrix (Fin 3) (Fin 3) ℂ := 1
  have hI : I₃ᴴ * I₃ = 1 := by simp [I₃]
  let D := embed₃ I₃ U I₃ C
  have hDr : D.rank ≤ 2 := (productRay_rank_embed₃ hI hU hI C).trans_le hC
  have hDz : endpointEnergy D = 0 := (productRay_endpointEnergy_embed₃ hI hU hI C).trans hz
  have hDN : frobSq D = 1 := (frobSq_embed₃ hI hU hI C).trans hN
  have hDrow : ∀ i, i ≠ k → ∀ r q, D (i, r) q = 0 := by
    dsimp [D, I₃]
    rw [embed₃_eq_mul]
    exact first_output_coordinate_conj_remaining C (U ⊗ₖ 1) k hrow
  have hblock : firstSiteBlock D k j₀ =
      (U ⊗ₖ I₃) * firstSiteBlock C k j₀ * (U ⊗ₖ I₃)ᴴ := by
    dsimp [D, I₃]
    rw [embed₃_eq_mul, firstSiteBlock_conj_remaining]
  have hDne : firstSiteBlock D k j₀ ≠ 0 := by
    intro he
    have hrec := twoCut_unitary_conj_recover (U ⊗ₖ I₃) (firstSiteBlock C k j₀)
      (kron_isometry U I₃ hU hI)
    rw [← hblock, he, Matrix.mul_zero, Matrix.zero_mul] at hrec
    exact hne hrec.symm
  have hDanchor : ∀ i, i ≠ 0 → ∀ r q, firstSiteBlock D k j₀ (i, r) q = 0 := by
    rw [hblock]
    exact hArow
  have hDsecond := single_output_anchor_coordinate_propagates D hDr hDz k j₀ 0
    hDrow hDne hDanchor
  have hmember := isQutritZeroFamilyMember_of_two_output_coordinates D hDr hDz hDN
    k 0 hDrow hDsecond
  exact (isQutritZeroFamilyMember_local_unitary_iff I₃ U I₃ hI hU hI C).mp hmember

end ThreeCopyQutritWerner
