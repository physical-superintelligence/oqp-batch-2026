module

public import ThreeCopyQutritWerner.ThinFirstSiteAnchor
public import ThreeCopyQutritWerner.ThinPencilFreeInput

@[expose] public section


/-!
# The identically-zero free pencil is exactly the scalar-plane branch

The two independent complex parameters retain both off-plane input blocks.
Their vanishing, as actual matrices, leaves the original plane projector
tensor an unrestricted two-qutrit matrix.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Kronecker

namespace ThreeCopyQutritWerner

theorem firstSiteContraction_free_pencil_coordinates
    {d : Type*} [Fintype d] [DecidableEq d]
    (C : Matrix (Fin 3 × d) (Fin 3 × d) ℂ) (z t : ℂ) :
    firstSiteContraction C ![1, conj z, 0] ![-z, 1, conj t] =
      firstSiteBlock C 0 1 + z • (firstSiteBlock C 1 1 - firstSiteBlock C 0 0) -
        z ^ 2 • firstSiteBlock C 1 0 +
        conj t • (firstSiteBlock C 0 2 + z • firstSiteBlock C 1 2) := by
  ext r s
  simp [firstSiteContraction_apply, Fin.sum_univ_three, firstSiteBlock,
    Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem thinFirstSite_free_pencil_all_zero_scalar_plane
    (C : Matrix QutritSites QutritSites ℂ)
    (hrow : ∀ r q, C (2, r) q = 0)
    (h : ∀ z t : ℂ, firstSiteContraction C ![1, conj z, 0] ![-z, 1, conj t] = 0) :
    C = (qutritPlaneInclusion 2 * (qutritPlaneInclusion 2)ᴴ) ⊗ₖ
      firstSiteBlock C 0 0 := by
  have hentry (z t : ℂ) (r s : Fin 3 × Fin 3) :
      firstSiteBlock C 0 1 r s + z * (firstSiteBlock C 1 1 r s - firstSiteBlock C 0 0 r s) -
        z ^ 2 * firstSiteBlock C 1 0 r s +
        conj t * (firstSiteBlock C 0 2 r s + z * firstSiteBlock C 1 2 r s) = 0 := by
    have he := h z t
    rw [firstSiteContraction_free_pencil_coordinates] at he
    simpa only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply] using congrFun (congrFun he r) s
  have h01 : firstSiteBlock C 0 1 = 0 := by
    ext r s
    simpa using hentry 0 0 r s
  have h02 : firstSiteBlock C 0 2 = 0 := by
    ext r s
    simpa [h01] using hentry 0 1 r s
  have h10 : firstSiteBlock C 1 0 = 0 := by
    ext r s
    have hp := hentry 1 0 r s
    have hm := hentry (-1) 0 r s
    simp only [map_zero, map_one, h01, Matrix.zero_apply, one_mul, zero_mul,
      zero_add, add_zero, one_pow, neg_one_mul, neg_one_sq] at hp hm
    change firstSiteBlock C 1 0 r s = 0
    linear_combination -(hp + hm) / 2
  have hd : firstSiteBlock C 0 0 = firstSiteBlock C 1 1 := by
    ext r s
    have hp := hentry 1 0 r s
    simp only [map_zero, h01, h10, Matrix.zero_apply, one_mul, zero_mul,
      zero_add, add_zero, one_pow, sub_zero] at hp
    exact (sub_eq_zero.mp hp).symm
  have h12 : firstSiteBlock C 1 2 = 0 := by
    ext r s
    simpa [h01, h02, h10, ← hd] using hentry 1 1 r s
  apply thinFirstSiteAnchor_all_zero_scalar_plane C hrow
  intro i
  fin_cases i
  · exact h02
  · exact h12
  · exact h01
  · exact h10
  · change firstSiteContraction C ![1, 1, 0] ![1, -1, 0] = 0
    rw [(firstSiteContraction_pauli_coordinates C).1, h10, h01, ← hd]
    simp

/-- No nonzero-pencil premise is lost: if it fails for all free input
coefficients, the original normalized matrix is already family I. -/
theorem thinFirstSite_family_or_nonzero_free_pencil
    (X Y : Matrix QutritSites (Fin 2) ℂ) (hC : (X * Yᴴ).rank ≤ 2)
    (hN : frobSq (X * Yᴴ) = 1) (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) :
    IsQutritZeroFamilyMember (X * Yᴴ) ∨ ∃ z t : ℂ,
      (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1) *
        (firstSiteFactorBlock Y 1 - conj z • firstSiteFactorBlock Y 0 +
          t • firstSiteFactorBlock Y 2)ᴴ ≠ 0 := by
  by_cases h : ∀ z t : ℂ,
      firstSiteContraction (X * Yᴴ) ![1, conj z, 0] ![-z, 1, conj t] = 0
  · left
    exact isQutritZeroFamilyMember_of_scalar_plane_tensor (X * Yᴴ) hC hN
      (qutritPlaneInclusion 2) (qutritPlaneInclusion_isometry 2)
      (firstSiteBlock (X * Yᴴ) 0 0)
      (thinFirstSite_free_pencil_all_zero_scalar_plane (X * Yᴴ) hrow h)
  · push_neg at h
    obtain ⟨z, t, hzt⟩ := h
    refine Or.inr ⟨z, t, ?_⟩
    rwa [firstSiteFactor_free_input_product]

end ThreeCopyQutritWerner
