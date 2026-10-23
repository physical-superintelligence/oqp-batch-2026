module

public import ThreeCopyQutritWerner.ZeroRelations

@[expose] public section


/-!
# Equation (24) on the complete known zero-family union

A common one-dimensional local factor of the source columns forces both the bivector and
`H` to be symmetric under the swap at that site. This proves the zero relations for family II,
including all three placements. Together with the scalar-idempotent identities for families I
and III, this gives the relations for every `IsQutritZeroFamilyMember`, with its unit phase,
and every width-two factorization.

This is the known-family direction only. Deducing (24) for an arbitrary endpoint zero still
requires the saturated certificate kernel and the linear maps on holomorphic feature space.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

section CommonFactor

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- Disjoint local antisymmetrizers commute. -/
theorem siteAnti₁_siteAnti₂ (M : Matrix (a × b × c) (a × b × c) ℂ) :
    siteAnti₁ (siteAnti₂ M) = siteAnti₂ (siteAnti₁ M) := by
  ext r s
  simp only [siteAnti₁, siteAnti₂, Matrix.of_apply, siteSwap₁, siteSwap₂, Equiv.coe_fn_mk]
  ring

theorem siteAnti₁_siteAnti₃ (M : Matrix (a × b × c) (a × b × c) ℂ) :
    siteAnti₁ (siteAnti₃ M) = siteAnti₃ (siteAnti₁ M) := by
  ext r s
  simp only [siteAnti₁, siteAnti₃, Matrix.of_apply, siteSwap₁, siteSwap₃, Equiv.coe_fn_mk]
  ring

theorem siteAnti₂_siteAnti₃ (M : Matrix (a × b × c) (a × b × c) ℂ) :
    siteAnti₂ (siteAnti₃ M) = siteAnti₃ (siteAnti₂ M) := by
  ext r s
  simp only [siteAnti₂, siteAnti₃, Matrix.of_apply, siteSwap₂, siteSwap₃, Equiv.coe_fn_mk]
  ring

/-- Any quadratic source expression is locally symmetric when its source columns share a
site-1 factor. No orthogonality or normalization is needed. -/
theorem siteAnti₁_source_quadratic (X : Matrix (a × b × c) (Fin 2) ℂ)
    (u : a → ℂ) (Y : Matrix (b × c) (Fin 2) ℂ)
    (hX : ∀ r k, X r k = u r.1 * Y r.2 k)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    siteAnti₁ (z • (X * M * Xᵀ)) = 0 := by
  ext r s
  simp only [siteAnti₁, Matrix.of_apply, siteSwap₁, Equiv.coe_fn_mk, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, hX,
    Matrix.zero_apply]
  ring

theorem siteAnti₂_source_quadratic (X : Matrix (a × b × c) (Fin 2) ℂ)
    (u : b → ℂ) (Y : Matrix (a × c) (Fin 2) ℂ)
    (hX : ∀ r k, X r k = u r.2.1 * Y (r.1, r.2.2) k)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    siteAnti₂ (z • (X * M * Xᵀ)) = 0 := by
  ext r s
  simp only [siteAnti₂, Matrix.of_apply, siteSwap₂, Equiv.coe_fn_mk, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, hX,
    Matrix.zero_apply]
  ring

theorem siteAnti₃_source_quadratic (X : Matrix (a × b × c) (Fin 2) ℂ)
    (u : c → ℂ) (Y : Matrix (a × b) (Fin 2) ℂ)
    (hX : ∀ r k, X r k = u r.2.2 * Y (r.1, r.2.1) k)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    siteAnti₃ (z • (X * M * Xᵀ)) = 0 := by
  ext r s
  simp only [siteAnti₃, Matrix.of_apply, siteSwap₃, Equiv.coe_fn_mk, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, hX,
    Matrix.zero_apply]
  ring

/-- A source with a common site-1 factor satisfies (24) for every right factor. -/
theorem zeroRelations_of_source_factor₁ (X : Matrix (a × b × c) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (a × b × c) ℂ) (u : a → ℂ)
    (Y : Matrix (b × c) (Fin 2) ℂ) (hX : ∀ r k, X r k = u r.1 * Y r.2 k) :
    ZeroRelations (hFeature (X * B) (bivecMat X)) (bivecMat X) := by
  have hp : siteAnti₁ (bivecMat X) = 0 := by
    exact siteAnti₁_source_quadratic X u Y hX epsMat _
  have hH : siteAnti₁ (hFeature (X * B) (bivecMat X)) = 0 := by
    rw [hFeature_formula]
    exact siteAnti₁_source_quadratic X u Y hX _ _
  apply zeroRelations_of_cases (Or.inr hp)
  · exact Or.inl (by rw [siteAnti₁_siteAnti₃, hH, siteAnti₃_zero])
  · exact Or.inl (by rw [siteAnti₁_siteAnti₂, hH, siteAnti₂_zero])

theorem zeroRelations_of_source_factor₂ (X : Matrix (a × b × c) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (a × b × c) ℂ) (u : b → ℂ)
    (Y : Matrix (a × c) (Fin 2) ℂ)
    (hX : ∀ r k, X r k = u r.2.1 * Y (r.1, r.2.2) k) :
    ZeroRelations (hFeature (X * B) (bivecMat X)) (bivecMat X) := by
  have hp : siteAnti₂ (bivecMat X) = 0 := by
    exact siteAnti₂_source_quadratic X u Y hX epsMat _
  have hH : siteAnti₂ (hFeature (X * B) (bivecMat X)) = 0 := by
    rw [hFeature_formula]
    exact siteAnti₂_source_quadratic X u Y hX _ _
  exact zeroRelations_of_cases (Or.inl (by rw [siteAnti₂_siteAnti₃, hH, siteAnti₃_zero]))
    (Or.inr hp) (Or.inl (by rw [hH, siteAnti₁_zero]))

theorem zeroRelations_of_source_factor₃ (X : Matrix (a × b × c) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (a × b × c) ℂ) (u : c → ℂ)
    (Y : Matrix (a × b) (Fin 2) ℂ)
    (hX : ∀ r k, X r k = u r.2.2 * Y (r.1, r.2.1) k) :
    ZeroRelations (hFeature (X * B) (bivecMat X)) (bivecMat X) := by
  have hp : siteAnti₃ (bivecMat X) = 0 := by
    exact siteAnti₃_source_quadratic X u Y hX epsMat _
  have hH : siteAnti₃ (hFeature (X * B) (bivecMat X)) = 0 := by
    rw [hFeature_formula]
    exact siteAnti₃_source_quadratic X u Y hX _ _
  exact zeroRelations_of_cases (Or.inl (by rw [hH, siteAnti₂_zero]))
    (Or.inl (by rw [hH, siteAnti₁_zero])) (Or.inr hp)

/-- A rank-two factorization inherits any common local factor of the range of `C`. -/
theorem zeroRelations_of_range_factor₁ (C : Matrix (a × b × c) (a × b × c) ℂ)
    (hr : C.rank = 2) (u : a → ℂ) (K : Matrix (b × c) (a × b × c) ℂ)
    (hC : ∀ r s, C r s = u r.1 * K r.2 s)
    (X : Matrix (a × b × c) (Fin 2) ℂ) (B : Matrix (Fin 2) (a × b × c) ℂ)
    (hXB : C = X * B) : ZeroRelations (hFeature C (bivecMat X)) (bivecMat X) := by
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_eq_two B
    (rank_eq_two_of_mul X B (hXB ▸ hr)).2
  have hXR : X = C * R := by rw [hXB, Matrix.mul_assoc, hR, Matrix.mul_one]
  rw [hXB]
  apply zeroRelations_of_source_factor₁ X B u (K * R)
  intro r k
  rw [hXR]
  simp only [Matrix.mul_apply, hC, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem zeroRelations_of_range_factor₂ (C : Matrix (a × b × c) (a × b × c) ℂ)
    (hr : C.rank = 2) (u : b → ℂ) (K : Matrix (a × c) (a × b × c) ℂ)
    (hC : ∀ r s, C r s = u r.2.1 * K (r.1, r.2.2) s)
    (X : Matrix (a × b × c) (Fin 2) ℂ) (B : Matrix (Fin 2) (a × b × c) ℂ)
    (hXB : C = X * B) : ZeroRelations (hFeature C (bivecMat X)) (bivecMat X) := by
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_eq_two B
    (rank_eq_two_of_mul X B (hXB ▸ hr)).2
  have hXR : X = C * R := by rw [hXB, Matrix.mul_assoc, hR, Matrix.mul_one]
  rw [hXB]
  apply zeroRelations_of_source_factor₂ X B u (K * R)
  intro r k
  rw [hXR]
  simp only [Matrix.mul_apply, hC, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem zeroRelations_of_range_factor₃ (C : Matrix (a × b × c) (a × b × c) ℂ)
    (hr : C.rank = 2) (u : c → ℂ) (K : Matrix (a × b) (a × b × c) ℂ)
    (hC : ∀ r s, C r s = u r.2.2 * K (r.1, r.2.1) s)
    (X : Matrix (a × b × c) (Fin 2) ℂ) (B : Matrix (Fin 2) (a × b × c) ℂ)
    (hXB : C = X * B) : ZeroRelations (hFeature C (bivecMat X)) (bivecMat X) := by
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_eq_two B
    (rank_eq_two_of_mul X B (hXB ▸ hr)).2
  have hXR : X = C * R := by rw [hXB, Matrix.mul_assoc, hR, Matrix.mul_one]
  rw [hXB]
  apply zeroRelations_of_source_factor₃ X B u (K * R)
  intro r k
  rw [hXR]
  simp only [Matrix.mul_apply, hC, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

end CommonFactor

section KnownFamilies

open scoped Kronecker

/-- Scalar-idempotence is preserved by arbitrary complex rescaling. -/
theorem smul_mul_self_of_mul_self {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) (z κ : ℂ) (h : M * M = κ • M) :
    (z • M) * (z • M) = (z * κ) • (z • M) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, h]
  simp only [smul_smul]
  congr 1
  ring

/-- Family II, including an arbitrary scalar and site-1 placement, obeys (24) whenever its
rank is two. The endpoint and binary-isometry conditions are unnecessary for this algebra. -/
theorem zeroRelations_smul_familyII (a b : Fin 3 → ℂ)
    (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) (z : ℂ)
    (hr : (z • familyII a b U V₂ V₃).rank = 2)
    (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hXB : z • familyII a b U V₂ V₃ = X * B) :
    ZeroRelations (hFeature (z • familyII a b U V₂ V₃) (bivecMat X)) (bivecMat X) := by
  apply zeroRelations_of_range_factor₁ _ hr a
    (fun r s => z * (starRingEnd ℂ) (b s.1) *
      ((V₂ ⊗ₖ V₃) * binaryB₂ U * (V₂ ⊗ₖ V₃)ᴴ) r s.2) _ X B hXB
  intro r s
  simp only [Matrix.smul_apply, smul_eq_mul, familyII, tensor₂, Matrix.of_apply, ketBra]
  ring

theorem zeroRelations_smul_familyII_site₂ (a b : Fin 3 → ℂ)
    (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) (z : ℂ)
    (hr : (z • (familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm).rank = 2)
    (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hXB : z • (familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm = X * B) :
    ZeroRelations (hFeature
      (z • (familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm) (bivecMat X))
      (bivecMat X) := by
  apply zeroRelations_of_range_factor₂ _ hr a
    (fun r s => z * (starRingEnd ℂ) (b s.2.1) *
      ((V₂ ⊗ₖ V₃) * binaryB₂ U * (V₂ ⊗ₖ V₃)ᴴ) r (s.1, s.2.2)) _ X B hXB
  intro r s
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, familyII, tensor₂,
    Matrix.of_apply, ketBra, siteEquiv₂, Equiv.symm_mk, Equiv.coe_fn_mk]
  ring

theorem zeroRelations_smul_familyII_site₃ (a b : Fin 3 → ℂ)
    (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) (z : ℂ)
    (hr : (z • (familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm).rank = 2)
    (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hXB : z • (familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm = X * B) :
    ZeroRelations (hFeature
      (z • (familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm) (bivecMat X))
      (bivecMat X) := by
  apply zeroRelations_of_range_factor₃ _ hr a
    (fun r s => z * (starRingEnd ℂ) (b s.2.2) *
      ((V₂ ⊗ₖ V₃) * binaryB₂ U * (V₂ ⊗ₖ V₃)ᴴ) r (s.1, s.2.1)) _ X B hXB
  intro r s
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, familyII, tensor₂,
    Matrix.of_apply, ketBra, siteEquiv₃, Equiv.symm_mk, Equiv.coe_fn_mk]
  ring

/-- Equation (24) holds on the whole known-family union, at every placement and unit phase,
for every width-two factorization. This does not assert that every endpoint zero belongs to the
known union or that its holomorphic feature lies in the span of known zero features. -/
theorem zeroRelations_of_isQutritZeroFamilyMember
    {C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ}
    (hC : IsQutritZeroFamilyMember C)
    (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ) (hXB : C = X * B) :
    ZeroRelations (hFeature C (bivecMat X)) (bivecMat X) := by
  have hr := rank_eq_two_of_isQutritZeroFamilyMember hC
  obtain ⟨z, hz, D, rfl, hD⟩ := hC
  rcases hD with ⟨f₁, f₂, χ, η, h1, h2, h12, hχ, hη, hD⟩ |
      ⟨a, b, U, V₂, V₃, ha, hb, hU, h₂, h₃, hD⟩ |
      ⟨U, V₁, V₂, V₃, hU, h₁, h₂, h₃, rfl⟩
  · rcases hD with rfl | rfl | rfl
    · exact zeroRelations_of_sq_of_rank _ hr _
        (smul_mul_self_of_mul_self _ z _ (familyIMat_mul_self f₁ f₂ χ η h1 h2 h12)) X B hXB
    · exact zeroRelations_of_sq_of_rank _ hr _
        (smul_mul_self_of_mul_self _ z _ (submatrix_mul_self_of_mul_self _ _ _
          (familyIMat_mul_self f₁ f₂ χ η h1 h2 h12))) X B hXB
    · exact zeroRelations_of_sq_of_rank _ hr _
        (smul_mul_self_of_mul_self _ z _ (submatrix_mul_self_of_mul_self _ _ _
          (familyIMat_mul_self f₁ f₂ χ η h1 h2 h12))) X B hXB
  · rcases hD with rfl | rfl | rfl
    · exact zeroRelations_smul_familyII a b U V₂ V₃ z hr X B hXB
    · exact zeroRelations_smul_familyII_site₂ a b U V₂ V₃ z hr X B hXB
    · exact zeroRelations_smul_familyII_site₃ a b U V₂ V₃ z hr X B hXB
  · exact zeroRelations_of_sq_of_rank _ hr _
      (smul_mul_self_of_mul_self _ z _ (familyIII_mul_self U V₁ V₂ V₃ h₁ h₂ h₃)) X B hXB

end KnownFamilies

end ThreeCopyQutritWerner

end
