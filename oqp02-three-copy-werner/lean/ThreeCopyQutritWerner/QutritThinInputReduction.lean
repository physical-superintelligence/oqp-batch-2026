module

public import ThreeCopyQutritWerner.QutritThinPhysicalFrame
public import ThreeCopyQutritWerner.FirstSiteInputSplit
public import ThreeCopyQutritWerner.ProductRayUnitary

@[expose] public section


/-!
# Actual unitary coordinates for the thin-input block reduction

The unitary and missing output row are constructed from the original local
range dimension. Rank, endpoint energy and Frobenius norm are unchanged.
The final off-plane cut-zero consequence keeps endpoint positivity explicit.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- A thin first local range has actual unitary coordinates with a missing
output row, while preserving all original scalar data. -/
theorem qutrit_thin_first_exists_unitary_missing_row
    (C : Matrix QutritSites QutritSites ℂ) (hthin : localRangeDim₁ C ≤ 2) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℂ) (k : Fin 3), Uᴴ * U = 1 ∧
      (∀ r q, (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C) (k, r) q = 0) ∧
      (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C).rank = C.rank ∧
      endpointEnergy (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C) = endpointEnergy C ∧
      frobSq (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C) = frobSq C := by
  rw [localRangeDim₁_eq_coherentFlatten_rank] at hthin
  obtain ⟨U, k, hU, hk⟩ :=
    qutrit_rank_le_two_exists_unitary_zero_row (coherentFlatten₁ C) hthin
  have hI : (1 : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * 1 = 1 := by simp
  refine ⟨U, k, hU, ?_, productRay_rank_embed₃ hU hI hI C,
    productRay_endpointEnergy_embed₃ hU hI hI C, frobSq_embed₃ hU hI hI C⟩
  let K := U ⊗ₖ (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
  have hleft : ∀ r q, (K * C) (k, r) q = 0 := by
    intro r q
    have h := hk (r, q)
    simpa [K, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Prod.mk.injEq, coherentFlatten₁] using h
  have he : embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C = K * C * Kᴴ := by
    simp only [embed₃_eq_mul, Matrix.one_kronecker_one, K]
  intro r q
  rw [he, Matrix.mul_apply]
  simp only [hleft, zero_mul, Finset.sum_const_zero]

/-- REDUCTION: a thin original qutrit endpoint zero supplies actual off-plane
two-site cut zeros after a constructed energy-preserving unitary change. -/
theorem qutrit_thin_first_offplane_cut_zeros
    (hendpoint : QutritEndpointInequality)
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hthin : localRangeDim₁ C ≤ 2) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℂ) (k : Fin 3), Uᴴ * U = 1 ∧
      (∀ r q, (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C) (k, r) q = 0) ∧
      (∀ i, cutForm (firstSiteBlock (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C) i k) = 0) ∧
      endpointEnergy (firstSiteInputDrop (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C) k) = 0 := by
  obtain ⟨U, k, hU, hrow, hr, he, _⟩ :=
    qutrit_thin_first_exists_unitary_missing_row C hthin
  have hD : (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C).rank ≤ 2 := hr.trans_le hC
  have hDz : endpointEnergy (embed₃ (b' := Fin 3) (c' := Fin 3) U 1 1 C) = 0 := he.trans hz
  refine ⟨U, k, hU, hrow, ?_, ?_⟩
  · exact firstSiteBlock_cutForm_zero_of_endpoint_zero hendpoint _ hD hDz k hrow
  · exact (endpointEnergy_firstSiteInputSplit_zero hendpoint _ hD hDz k hrow).2

end ThreeCopyQutritWerner
