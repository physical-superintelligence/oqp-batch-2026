module

public import ThreeCopyQutritWerner.CertificateX2IntegrationSources

@[expose] public section


/-!
# Symmetry of the concrete source blocks; trial blocks as Gram products

For the input stage (theorems with hypotheses `hsym : ∀ k, (N k)ᵀ = N k` and
`N k = ((1 / 2 ^ 80 : ℚ) • F.map Int.cast) * ((1 / 2 ^ 80 : ℚ) • F.map Int.cast)ᵀ`):
* `x2Trial_eq_gram`: every trial block is the Gram product of `(1 / 2 ^ 80) • x2TrialFactor s b`;
* `x2Trial_transpose`, `x2SourceM_transpose`, `x2SourceA_transpose`: every source block is symmetric (the corrected blocks
  through the symmetry of the face literal `A`, read off the Hermitian part of its certificate
  `A_psd`, so no new kernel computation).
The form with `X2.x2FactorOf` is in CertificateX2IntegrationSourcesFactor.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The trial block as a Gram product of the scaled packed factor. -/
theorem x2Trial_eq_gram (s : Fin 3) (b : x2Key s) :
    x2Trial s b = ((1 / 2 ^ 80 : ℚ) • (x2TrialFactor s b).map (Int.cast : ℤ → ℚ)) *
      ((1 / 2 ^ 80 : ℚ) • (x2TrialFactor s b).map (Int.cast : ℤ → ℚ))ᵀ := by
  rw [x2Trial_apply]
  have hmap : (x2TrialFactor s b * (x2TrialFactor s b)ᵀ).map (Int.cast : ℤ → ℚ) =
      (x2TrialFactor s b).map (Int.cast : ℤ → ℚ) * ((x2TrialFactor s b).map (Int.cast : ℤ → ℚ))ᵀ := by
    change (x2TrialFactor s b * (x2TrialFactor s b)ᵀ).map (Int.castRingHom ℚ) =
      (x2TrialFactor s b).map (Int.castRingHom ℚ) * ((x2TrialFactor s b).map (Int.castRingHom ℚ))ᵀ
    rw [Matrix.map_mul, Matrix.transpose_map]
  have hc : (1 / ((2 ^ 80 : ℤ) : ℚ)) ^ 2 = (1 / 2 ^ 80 : ℚ) * (1 / 2 ^ 80 : ℚ) := by norm_num
  rw [hmap, hc, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- Every trial block is symmetric. -/
theorem x2Trial_transpose (s : Fin 3) (b : x2Key s) : (x2Trial s b)ᵀ = x2Trial s b := by
  rw [x2Trial_eq_gram, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- An integer matrix whose complex cast is positive semidefinite is symmetric. -/
theorem x2_int_symm_of_psd {n : Type*} [Fintype n] (A : Matrix n n ℤ)
    (hA : (A.map (Int.castRingHom ℂ)).PosSemidef) : Aᵀ = A := by
  ext i j
  have h := congrFun (congrFun hA.isHermitian.eq i) j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Int.coe_castRingHom, star_intCast] at h
  rw [Matrix.transpose_apply]
  exact_mod_cast h

/-- A congruence `K (c A) Kᵀ` of a symmetric integer matrix is symmetric. -/
theorem x2_congr_symm {r k : Type*} [Fintype k] (K : Matrix r k ℤ) (A : Matrix k k ℤ) (c : ℚ) (hA : Aᵀ = A) :
    (K.map (Int.cast : ℤ → ℚ) * (c • A.map (Int.cast : ℤ → ℚ)) * (K.map (Int.cast : ℤ → ℚ))ᵀ)ᵀ =
      K.map (Int.cast : ℤ → ℚ) * (c • A.map (Int.cast : ℤ → ℚ)) * (K.map (Int.cast : ℤ → ℚ))ᵀ := by
  have hX : (c • A.map (Int.cast : ℤ → ℚ))ᵀ = c • A.map (Int.cast : ℤ → ℚ) := by
    rw [Matrix.transpose_smul, ← Matrix.transpose_map, hA]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hX, Matrix.mul_assoc]

namespace X2Src

theorem blk1x006k0_transpose : (blk1x006k0)ᵀ = blk1x006k0 :=
  x2_congr_symm K1x006k0 X2Correction1x006k0Face.A (1 / ((x2CorrDen : ℤ) : ℚ))
    (x2_int_symm_of_psd X2Correction1x006k0Face.A X2Correction1x006k0Face.A_psd)

theorem blk1x036k0_transpose : (blk1x036k0)ᵀ = blk1x036k0 :=
  x2_congr_symm K1x036k0 X2Correction1x036k0Face.A (1 / ((x2CorrDen : ℤ) : ℚ))
    (x2_int_symm_of_psd X2Correction1x036k0Face.A X2Correction1x036k0Face.A_psd)

theorem blk1x116k0_transpose : (blk1x116k0)ᵀ = blk1x116k0 :=
  x2_congr_symm K1x116k0 X2Correction1x116k0Face.A (1 / ((x2CorrDen : ℤ) : ℚ))
    (x2_int_symm_of_psd X2Correction1x116k0Face.A X2Correction1x116k0Face.A_psd)

theorem blk1x346k0_transpose : (blk1x346k0)ᵀ = blk1x346k0 :=
  x2_congr_symm K1x346k0 X2Correction1x346k0Face.A (1 / ((x2CorrDen : ℤ) : ℚ))
    (x2_int_symm_of_psd X2Correction1x346k0Face.A X2Correction1x346k0Face.A_psd)

theorem blk1x444k0_transpose : (blk1x444k0)ᵀ = blk1x444k0 :=
  x2_congr_symm K1x444k0 X2Correction1x444k0Face.A (1 / ((x2CorrDen : ℤ) : ℚ))
    (x2_int_symm_of_psd X2Correction1x444k0Face.A X2Correction1x444k0Face.A_psd)

theorem blk1x456k0_transpose : (blk1x456k0)ᵀ = blk1x456k0 :=
  x2_congr_symm K1x456k0 X2Correction1x456k0Face.A (1 / ((x2CorrDen : ℤ) : ℚ))
    (x2_int_symm_of_psd X2Correction1x456k0Face.A X2Correction1x456k0Face.A_psd)

theorem blk1x555k0_transpose : (blk1x555k0)ᵀ = blk1x555k0 :=
  x2_congr_symm K1x555k0 X2Correction1x555k0Face.A (1 / ((x2CorrDen : ℤ) : ℚ))
    (x2_int_symm_of_psd X2Correction1x555k0Face.A X2Correction1x555k0Face.A_psd)

theorem blk2x146k0_transpose : (blk2x146k0)ᵀ = blk2x146k0 :=
  x2_congr_symm K2x146k0 X2Correction2x146k0Face.A (1 / ((x2CorrDen : ℤ) : ℚ))
    (x2_int_symm_of_psd X2Correction2x146k0Face.A X2Correction2x146k0Face.A_psd)

end X2Src

/-- Every concrete source block of sector m is symmetric. -/
theorem x2SourceM_transpose : ∀ b, (x2SourceM b)ᵀ = x2SourceM b := by
  intro b
  by_cases h : b ∈ x2CorrKeysM
  · simp only [x2CorrKeysM, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [x2SourceM_k1x006k0]
      exact X2Src.blk1x006k0_transpose
    · rw [x2SourceM_k1x036k0]
      exact X2Src.blk1x036k0_transpose
    · rw [x2SourceM_k1x116k0]
      exact X2Src.blk1x116k0_transpose
    · rw [x2SourceM_k1x346k0]
      exact X2Src.blk1x346k0_transpose
    · rw [x2SourceM_k1x444k0]
      exact X2Src.blk1x444k0_transpose
    · rw [x2SourceM_k1x456k0]
      exact X2Src.blk1x456k0_transpose
    · rw [x2SourceM_k1x555k0]
      exact X2Src.blk1x555k0_transpose
  · rw [x2SourceM_of_not_mem b h]
    exact x2Trial_transpose 1 b

/-- Every concrete source block of sector a is symmetric. -/
theorem x2SourceA_transpose : ∀ b, (x2SourceA b)ᵀ = x2SourceA b := by
  intro b
  by_cases h : b ∈ x2CorrKeysA
  · simp only [x2CorrKeysA, Finset.mem_singleton] at h
    subst h
    rw [x2SourceA_k2x146k0]
    exact X2Src.blk2x146k0_transpose
  · rw [x2SourceA_of_not_mem b h]
    exact x2Trial_transpose 2 b

end ThreeCopyQutritWerner

end
