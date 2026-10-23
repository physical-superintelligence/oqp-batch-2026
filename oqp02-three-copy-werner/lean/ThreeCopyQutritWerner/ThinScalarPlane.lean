module

public import ThreeCopyQutritWerner.IdentityTensorRank
public import ThreeCopyQutritWerner.BinaryPartitionEmbedding
public import ThreeCopyQutritWerner.ProductRayUnitary

@[expose] public section


/-!
# The scalar-plane branch with arbitrary inactive two-qutrit rays

An actual plane-projector tensor factor and the original rank/norm data
force exactly family I. The other factor is a full nine-dimensional matrix;
its normalized rays are never assumed to have binary local support.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Normalize an actual plane tensor from its original matrix rank and norm.
All complex phase is absorbed into the unrestricted inactive ket vector. -/
theorem qutrit_scalar_plane_normalized_familyI
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2) (hN : frobSq C = 1)
    (J : Matrix (Fin 3) (Fin 2) ℂ) (hJ : Jᴴ * J = 1)
    (T : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (he : C = (J * Jᴴ) ⊗ₖ T) :
    ∃ χ η : Fin 3 × Fin 3 → ℂ, vecNormSq χ = 1 ∧ vecNormSq η = 1 ∧
      C = familyIMat (fun i => J i 0) (fun i => J i 1) χ η := by
  let I₉ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := 1
  have hI₉ : I₉ᴴ * I₉ = 1 := by simp [I₉]
  have hemb : (J ⊗ₖ I₉) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T) *
      (J ⊗ₖ I₉)ᴴ = C := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
    simpa [I₉] using he.symm
  have hr := productRay_rank_conj_isometry (J ⊗ₖ I₉)
    (kron_isometry J I₉ hJ hI₉) ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T)
  rw [hemb] at hr
  have hT : T.rank ≤ 1 := binary_identity_tensor_rank_le_one T (hr.symm.trans_le hC)
  have hP : frobSq (J * Jᴴ) = 2 := by
    have hn := frobSq_conj_isometry J hJ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    simpa [frobSq, Matrix.one_apply, Fin.sum_univ_two] using hn
  have hTN : frobSq T = 1 / 2 := by
    rw [he, ← tensor₂_eq_kronecker, frobSq_tensor₂, hP] at hN
    linarith
  obtain ⟨χ, η, hχ, hη, hTfact⟩ := binaryPartition_rank_one_half_norm T hT hTN
  refine ⟨χ, η, hχ, hη, ?_⟩
  rw [he, hTfact, Matrix.kronecker_smul, binaryPartition_two_column_projection]
  simp only [familyIMat, tensor₂_eq_kronecker, Matrix.smul_kronecker]

/-- This original-coordinate branch belongs to the exact family
predicate. No local-rank restriction is imposed on either inactive ray. -/
theorem isQutritZeroFamilyMember_of_scalar_plane_tensor
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2) (hN : frobSq C = 1)
    (J : Matrix (Fin 3) (Fin 2) ℂ) (hJ : Jᴴ * J = 1)
    (T : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (he : C = (J * Jᴴ) ⊗ₖ T) : IsQutritZeroFamilyMember C := by
  obtain ⟨χ, η, hχ, hη, hCeq⟩ := qutrit_scalar_plane_normalized_familyI C hC hN J hJ T he
  obtain ⟨h₀, h₁, h₀₁⟩ := binaryPartition_two_column_orthonormal J hJ
  refine ⟨1, by norm_num, C, by simp, Or.inl ?_⟩
  exact ⟨_, _, χ, η, h₀, h₁, h₀₁, hχ, hη, Or.inl hCeq⟩

end ThreeCopyQutritWerner
