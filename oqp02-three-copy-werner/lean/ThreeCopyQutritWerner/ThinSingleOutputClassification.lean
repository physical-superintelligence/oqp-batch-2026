module

public import ThreeCopyQutritWerner.ThinSingleOutputOtherFactor
public import ThreeCopyQutritWerner.ThinSingleOutputLine
public import ThreeCopyQutritWerner.TwoCutZeroPlanes

@[expose] public section


/-!
# Complete classification with one actual local output ray

One nonzero original block supplies the cut-zero anchor. Its two physical
output planes are constructed, then the two one-dimensional source-factor
branches and the nondegenerate scalar-line branch exhaust all possibilities.
Every coordinate change is undone on the exact family predicate.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Every normalized endpoint zero with a single first output coordinate
belongs to the exact original family union. No anchor, carrier, common plane
or classification premise is supplied. -/
theorem isQutritZeroFamilyMember_of_single_output_coordinate
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1) (k : Fin 3)
    (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0) :
    IsQutritZeroFamilyMember C := by
  have hCne : C ≠ 0 := by
    intro he
    simp [he, frobSq] at hN
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, firstSiteBlock C k j₀ ≠ 0 := by
    by_contra h
    push_neg at h
    apply hCne
    ext ⟨i, r⟩ ⟨j, s⟩
    by_cases hi : i = k
    · subst i
      exact congrFun (congrFun (h j) r) s
    · exact hrow i hi r (j, s)
  have hAq := firstSiteBlock_cutForm_zero_of_single_output_endpoint_zero C hC hz k hrow j₀
  have hAr := (firstSiteBlock_rank_le C k j₀).trans hC
  obtain ⟨U, V, a, b, hU, hV, hsupport⟩ :=
    cutForm_zero_exists_output_planes (firstSiteBlock C k j₀) hAr hAq
  let I₃ : Matrix (Fin 3) (Fin 3) ℂ := 1
  have hI : I₃ᴴ * I₃ = 1 := by simp [I₃]
  let D := embed₃ I₃ U V C
  have hDr : D.rank ≤ 2 := (productRay_rank_embed₃ hI hU hV C).trans_le hC
  have hDz : endpointEnergy D = 0 := (productRay_endpointEnergy_embed₃ hI hU hV C).trans hz
  have hDN : frobSq D = 1 := (frobSq_embed₃ hI hU hV C).trans hN
  have hDrow : ∀ i, i ≠ k → ∀ r q, D (i, r) q = 0 := by
    dsimp [D, I₃]
    rw [embed₃_eq_mul]
    exact first_output_coordinate_conj_remaining C (U ⊗ₖ V) k hrow
  have hblock : firstSiteBlock D k j₀ =
      (U ⊗ₖ V) * firstSiteBlock C k j₀ * (U ⊗ₖ V)ᴴ := by
    dsimp [D, I₃]
    rw [embed₃_eq_mul, firstSiteBlock_conj_remaining]
  have hDne : firstSiteBlock D k j₀ ≠ 0 := by
    intro he
    have hrec := twoCut_unitary_conj_recover (U ⊗ₖ V) (firstSiteBlock C k j₀)
      (kron_isometry U V hU hV)
    rw [← hblock, he, Matrix.mul_zero, Matrix.zero_mul] at hrec
    exact hj₀ hrec.symm
  have hDanchor : ∀ i j q, i = a ∨ j = b → firstSiteBlock D k j₀ (i, j) q = 0 := by
    intro i j q hij
    rw [hblock, Matrix.mul_apply]
    simp only [hsupport i j _ hij, zero_mul, Finset.sum_const_zero]
  have hmember : IsQutritZeroFamilyMember D := by
    by_cases hf : HasSingleFirstOutput (firstSiteBlock D k j₀)
    · exact isQutritZeroFamilyMember_of_single_output_anchor_factor D hDr hDz hDN
        k j₀ hDrow hDne hf
    · by_cases hs : HasSingleFirstOutput (twoCutSwap (firstSiteBlock D k j₀))
      · exact isQutritZeroFamilyMember_of_single_output_anchor_other_factor D hDr hDz hDN
          k j₀ hDrow hDne hs
      · exact isQutritZeroFamilyMember_of_single_output_nondegenerate_source D hDr hDz hDN
          k j₀ hDrow hDne a b hDanchor hf hs
  exact (isQutritZeroFamilyMember_local_unitary_iff I₃ U V hI hU hV C).mp hmember

/-- A literal single local output ray is sufficient in the original
coordinates; the unitary and its surviving coordinate are constructed. -/
theorem isQutritZeroFamilyMember_of_single_first_output
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1)
    (hfactor : HasSingleFirstOutput C) : IsQutritZeroFamilyMember C := by
  obtain ⟨i₀, x, hx, hf⟩ := hfactor
  obtain ⟨U, hU, hrow⟩ := twoCut_single_output_exists_unitary_coordinate C i₀ x hx hf
  let I₃ : Matrix (Fin 3) (Fin 3) ℂ := 1
  have hI : I₃ᴴ * I₃ = 1 := by simp [I₃]
  have hr := (productRay_rank_embed₃ hU hI hI C).trans_le hC
  have hq := (productRay_endpointEnergy_embed₃ hU hI hI C).trans hz
  have hn := (frobSq_embed₃ hU hI hI C).trans hN
  have hcoord : ∀ i, i ≠ 0 → ∀ r q, (embed₃ U I₃ I₃ C) (i, r) q = 0 := by
    simpa only [embed₃_eq_mul, I₃, Matrix.one_kronecker_one] using hrow
  have hm := isQutritZeroFamilyMember_of_single_output_coordinate
    (embed₃ U I₃ I₃ C) hr hq hn 0 hcoord
  exact (isQutritZeroFamilyMember_local_unitary_iff U I₃ I₃ hU hI hI C).mp hm

end ThreeCopyQutritWerner
