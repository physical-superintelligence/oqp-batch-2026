module

public import ThreeCopyQutritWerner.ThinCoordinateClassification
public import ThreeCopyQutritWerner.QutritThinInputReduction

@[expose] public section


/-!
# The original thin-source classification, AppC-3

The actual local range rank constructs a unitary missing output coordinate.
The complete coordinate classification is transported back through the
literal local unitary and physical site permutations. No endpoint inequality
or separate classification premise is assumed.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem qutrit_thin_first_exists_unitary_row_two
    (C : Matrix QutritSites QutritSites ℂ) (hthin : localRangeDim₁ C ≤ 2) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ, Uᴴ * U = 1 ∧
      ∀ (r : Fin 3 × Fin 3) (q : QutritSites), (embed₃ U 1 1 C) (2, r) q = 0 := by
  rw [localRangeDim₁_eq_coherentFlatten_rank] at hthin
  obtain ⟨U, k, hU, hk⟩ := qutrit_rank_le_two_exists_unitary_zero_row (coherentFlatten₁ C) hthin
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 2 k
  let V := U.submatrix σ id
  have hV : Vᴴ * V = 1 := isometry_submatrix_rows_equiv U hU σ
  have hv (j : (Fin 3 × Fin 3) × QutritSites) : (V * coherentFlatten₁ C) 2 j = 0 := by
    change (U * coherentFlatten₁ C) (σ 2) j = 0
    simpa only [σ, Equiv.swap_apply_left] using hk j
  refine ⟨V, hV, ?_⟩
  let K := V ⊗ₖ (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
  have hleft : ∀ r q, (K * C) (2, r) q = 0 := by
    intro r q
    simpa [K, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Prod.mk.injEq, coherentFlatten₁] using hv (r, q)
  have he : embed₃ V 1 1 C = K * C * Kᴴ := by
    simp only [embed₃_eq_mul, Matrix.one_kronecker_one, K]
  intro r q
  rw [he, Matrix.mul_apply]
  simp only [hleft, zero_mul, Finset.sum_const_zero]

theorem isQutritZeroFamilyMember_of_thin_first_localRange
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1)
    (hthin : localRangeDim₁ C ≤ 2) : IsQutritZeroFamilyMember C := by
  obtain ⟨U, hU, hrow⟩ := qutrit_thin_first_exists_unitary_row_two C hthin
  have hI : (1 : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * 1 = 1 := by simp
  have hm := isQutritZeroFamilyMember_of_missing_first_row_two (embed₃ U 1 1 C)
    ((productRay_rank_embed₃ hU hI hI C).trans_le hC)
    ((productRay_endpointEnergy_embed₃ hU hI hI C).trans hz)
    ((frobSq_embed₃ hU hI hI C).trans hN) hrow
  exact (isQutritZeroFamilyMember_local_unitary_iff U 1 1 hU hI hI C).mp hm

theorem isQutritZeroFamilyMember_of_thin_localRange
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1)
    (hthin : HasThinLocalRange C) : IsQutritZeroFamilyMember C := by
  rcases hthin with h | h | h
  · exact isQutritZeroFamilyMember_of_thin_first_localRange C hC hz hN h
  · apply (isQutritZeroFamilyMember_site_iff C 1).mp
    exact isQutritZeroFamilyMember_of_thin_first_localRange (C.submatrix siteEquiv₂ siteEquiv₂)
      ((Matrix.rank_submatrix C siteEquiv₂ siteEquiv₂).trans_le hC)
      ((energy_submatrix_siteEquiv₂ (1 / 2) C).trans hz)
      ((frobSq_submatrix_equiv siteEquiv₂ C).trans hN)
      ((localRangeDim₁_submatrix_site₂ C).trans_le h)
  · apply (isQutritZeroFamilyMember_site_iff C 2).mp
    exact isQutritZeroFamilyMember_of_thin_first_localRange (C.submatrix siteEquiv₃ siteEquiv₃)
      ((Matrix.rank_submatrix C siteEquiv₃ siteEquiv₃).trans_le hC)
      ((energy_submatrix_siteEquiv₃ (1 / 2) C).trans hz)
      ((frobSq_submatrix_equiv siteEquiv₃ C).trans hN)
      ((localRangeDim₁_submatrix_site₃ C).trans_le h)

theorem appCInput3_proved : AppCInput3 := by
  intro C hC hN hz hthin
  exact isQutritZeroFamilyMember_of_thin_localRange C hC hz hN hthin

end ThreeCopyQutritWerner
