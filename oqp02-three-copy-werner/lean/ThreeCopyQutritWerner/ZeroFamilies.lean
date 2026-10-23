module

public import ThreeCopyQutritWerner.BinaryZeros

@[expose] public section


/-!
# Theorem 5.1, inclusion "⊇": singular values and site placements

Contents:

* family II: `(C†C)² = (C†C)/2` (`familyII_sq`), and the placements with `|a⟩⟨b|` on site 2 or
  site 3 (`familyII_endpoint_zero_site₂/₃`, with their singular values);
* family I: `(C†C)² = (C†C)/2` for every placement (`familyI_sq`, `familyI_sq_site₂/₃`);
* the union of Theorem 5.1 (`IsQutritZeroFamilyMember`: families I and II at every placement,
  family III, times a unit phase) consists of normalized rank-≤-2 endpoint zeros with both
  nonzero singular values `1/√2` (`isNormalizedHalfSingularZero_of_isQutritZeroFamilyMember`).

With `N = 1`, `(C†C)² = (C†C)/2` says that `C†C` is half an orthogonal projection of trace 2,
i.e. `C` has exactly two nonzero singular values, both equal to `1/√2`.
-/

noncomputable section

open scoped Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

section KetBra

variable {ι : Type*} [Fintype ι]

theorem conjTranspose_ketBra (x y : ι → ℂ) : (ketBra x y)ᴴ = ketBra y x := by
  ext i j
  show star (x j * (starRingEnd ℂ) (y i)) = y i * (starRingEnd ℂ) (x j)
  rw [star_mul', ← starRingEnd_apply, ← starRingEnd_apply, starRingEnd_self_apply, mul_comm]

theorem ketBra_mul_ketBra (x y z w : ι → ℂ) :
    ketBra x y * ketBra z w = braket y z • ketBra x w := by
  ext i j
  simp only [Matrix.mul_apply, ketBra, braket, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- For unit `a`, `b`: `(|a⟩⟨b|)† |a⟩⟨b| = |b⟩⟨b|` is idempotent. -/
theorem ketBra_conjTranspose_mul_self_sq (a b : ι → ℂ) (ha : vecNormSq a = 1)
    (hb : vecNormSq b = 1) :
    (ketBra a b)ᴴ * ketBra a b * ((ketBra a b)ᴴ * ketBra a b) =
      (1 : ℂ) • ((ketBra a b)ᴴ * ketBra a b) := by
  have hk : (ketBra a b)ᴴ * ketBra a b = ketBra b b := by
    rw [conjTranspose_ketBra, ketBra_mul_ketBra, braket_self, ha, Complex.ofReal_one, one_smul]
  rw [hk, ketBra_mul_ketBra, braket_self, hb, Complex.ofReal_one]

/-- The projector onto an orthonormal pair is idempotent. -/
theorem proj_mul_proj (f₁ f₂ : ι → ℂ) (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1)
    (h12 : braket f₁ f₂ = 0) :
    (ketBra f₁ f₁ + ketBra f₂ f₂) * (ketBra f₁ f₁ + ketBra f₂ f₂) =
      ketBra f₁ f₁ + ketBra f₂ f₂ := by
  have h21 : braket f₂ f₁ = 0 := by
    rw [← conj_braket, h12, map_zero]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, ketBra_mul_ketBra, ketBra_mul_ketBra,
    ketBra_mul_ketBra, ketBra_mul_ketBra, braket_self, braket_self, h1, h2, h12, h21]
  simp

theorem proj_conjTranspose (f₁ f₂ : ι → ℂ) :
    (ketBra f₁ f₁ + ketBra f₂ f₂)ᴴ = ketBra f₁ f₁ + ketBra f₂ f₂ := by
  rw [Matrix.conjTranspose_add, conjTranspose_ketBra, conjTranspose_ketBra]

end KetBra

/-! ### Singular values of Kronecker products and reindexings -/

/-- If `(M†M)² = s M†M` and `(N†N)² = t N†N`, then `((M ⊗ N)†(M ⊗ N))² = s t (M ⊗ N)†(M ⊗ N)`. -/
theorem kronecker_conjTranspose_mul_self_sq {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ]
    [Fintype ι'] [Fintype κ'] (M : Matrix ι' ι ℂ) (N : Matrix κ' κ ℂ) (s t : ℂ)
    (hM : Mᴴ * M * (Mᴴ * M) = s • (Mᴴ * M)) (hN : Nᴴ * N * (Nᴴ * N) = t • (Nᴴ * N)) :
    (M ⊗ₖ N)ᴴ * (M ⊗ₖ N) * ((M ⊗ₖ N)ᴴ * (M ⊗ₖ N)) =
      (s * t) • ((M ⊗ₖ N)ᴴ * (M ⊗ₖ N)) := by
  have hC : (M ⊗ₖ N)ᴴ * (M ⊗ₖ N) = (Mᴴ * M) ⊗ₖ (Nᴴ * N) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  rw [hC, ← Matrix.mul_kronecker_mul, hM, hN, Matrix.smul_kronecker, Matrix.kronecker_smul,
    smul_smul]

/-- Reindexing rows and columns by the same equivalence preserves `(C†C)² = s C†C`. -/
theorem submatrix_conjTranspose_mul_self_sq {m n : Type*} [Fintype m] [Fintype n]
    (C : Matrix m m ℂ) (e : n ≃ m) (s : ℂ) (h : Cᴴ * C * (Cᴴ * C) = s • (Cᴴ * C)) :
    (C.submatrix e e)ᴴ * C.submatrix e e * ((C.submatrix e e)ᴴ * C.submatrix e e) =
      s • ((C.submatrix e e)ᴴ * C.submatrix e e) := by
  have hC : (C.submatrix e e)ᴴ * C.submatrix e e = (Cᴴ * C).submatrix e e := by
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  have hs : (s • (Cᴴ * C)).submatrix e e = s • ((Cᴴ * C).submatrix e e) := by
    ext x y
    rfl
  rw [hC, Matrix.submatrix_mul_equiv, h, hs]

/-! ### Family II -/

theorem binaryB₂_conjTranspose_mul_self (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) :
    (binaryB₂ U)ᴴ * binaryB₂ U = (1 / 2 : ℂ) •
      ((U * epsMat * Uᵀ * epsJ₂ᵀ)ᴴ * (U * epsMat * Uᵀ * epsJ₂ᵀ)) := by
  rw [binaryB₂, epsJ₂_inv, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, star_inv_sqrt_two_mul_self]

theorem binaryB₂_conjTranspose_mul_self_sq (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) :
    (binaryB₂ U)ᴴ * binaryB₂ U * ((binaryB₂ U)ᴴ * binaryB₂ U) =
      (1 / 2 : ℂ) • ((binaryB₂ U)ᴴ * binaryB₂ U) := by
  have hM := conjTranspose_mul_self_idem _
    (U_eps_Ut_partialIsometry U hU epsJ₂ᵀ epsJ₂_transpose_mul_conjTranspose)
  rw [binaryB₂_conjTranspose_mul_self, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM,
    smul_smul]

/-- Theorem 5.1, family II, singular values: `(C†C)² = (C†C)/2`. -/
theorem familyII_sq (a b : Fin 3 → ℂ) (ha : vecNormSq a = 1) (hb : vecNormSq b = 1)
    (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ)
    (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1) :
    (familyII a b U V₂ V₃)ᴴ * familyII a b U V₂ V₃ *
        ((familyII a b U V₂ V₃)ᴴ * familyII a b U V₂ V₃) =
      (1 / 2 : ℂ) • ((familyII a b U V₂ V₃)ᴴ * familyII a b U V₂ V₃) := by
  have hW := kron_isometry V₂ V₃ h₂ h₃
  have hX : ((V₂ ⊗ₖ V₃) * binaryB₂ U * (V₂ ⊗ₖ V₃)ᴴ)ᴴ * ((V₂ ⊗ₖ V₃) * binaryB₂ U * (V₂ ⊗ₖ V₃)ᴴ) *
      (((V₂ ⊗ₖ V₃) * binaryB₂ U * (V₂ ⊗ₖ V₃)ᴴ)ᴴ * ((V₂ ⊗ₖ V₃) * binaryB₂ U * (V₂ ⊗ₖ V₃)ᴴ)) =
      (1 / 2 : ℂ) •
        (((V₂ ⊗ₖ V₃) * binaryB₂ U * (V₂ ⊗ₖ V₃)ᴴ)ᴴ * ((V₂ ⊗ₖ V₃) * binaryB₂ U * (V₂ ⊗ₖ V₃)ᴴ)) := by
    rw [conjTranspose_conj_mul_conj _ hW, conj_mul_conj _ hW,
      binaryB₂_conjTranspose_mul_self_sq U hU, Matrix.mul_smul, Matrix.smul_mul]
  rw [familyII, tensor₂_eq_kronecker,
    kronecker_conjTranspose_mul_self_sq _ _ 1 (1 / 2) (ketBra_conjTranspose_mul_self_sq a b ha hb)
      hX, one_mul]

/-- Theorem 5.1, family II with `|a⟩⟨b|` on site 2. -/
theorem familyII_endpoint_zero_site₂ (a b : Fin 3 → ℂ) (ha : vecNormSq a = 1)
    (hb : vecNormSq b = 1) (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
    (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1) :
    ((familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm).rank ≤ 2 ∧
      invN ((familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm) = 1 ∧
      endpointEnergy ((familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm) = 0 ∧
      ((familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm)ᴴ *
          (familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm *
          (((familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm)ᴴ *
            (familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm) =
        (1 / 2 : ℂ) • (((familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm)ᴴ *
          (familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm) := by
  obtain ⟨hr, hN, hq⟩ :=
    endpoint_zero_transport₂ _ (familyII_endpoint_zero a b ha hb U hU V₂ V₃ h₂ h₃)
  exact ⟨hr, hN, hq, submatrix_conjTranspose_mul_self_sq _ _ _
    (familyII_sq a b ha hb U hU V₂ V₃ h₂ h₃)⟩

/-- Theorem 5.1, family II with `|a⟩⟨b|` on site 3. -/
theorem familyII_endpoint_zero_site₃ (a b : Fin 3 → ℂ) (ha : vecNormSq a = 1)
    (hb : vecNormSq b = 1) (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
    (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1) :
    ((familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm).rank ≤ 2 ∧
      invN ((familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm) = 1 ∧
      endpointEnergy ((familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm) = 0 ∧
      ((familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm)ᴴ *
          (familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm *
          (((familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm)ᴴ *
            (familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm) =
        (1 / 2 : ℂ) • (((familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm)ᴴ *
          (familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm) := by
  obtain ⟨hr, hN, hq⟩ :=
    endpoint_zero_transport₃ _ (familyII_endpoint_zero a b ha hb U hU V₂ V₃ h₂ h₃)
  exact ⟨hr, hN, hq, submatrix_conjTranspose_mul_self_sq _ _ _
    (familyII_sq a b ha hb U hU V₂ V₃ h₂ h₃)⟩

/-! ### Family I -/

/-- Theorem 5.1, family I, singular values: `C = (P_E/√2) ⊗ |χ⟩⟨η|` satisfies
`(C†C)² = (C†C)/2`. -/
theorem familyI_sq {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (f₁ f₂ : a → ℂ) (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) (h12 : braket f₁ f₂ = 0)
    (χ η : b × c → ℂ) (hχ : vecNormSq χ = 1) (hη : vecNormSq η = 1) :
    (tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂)) (ketBra χ η))ᴴ *
        tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂)) (ketBra χ η) *
        ((tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
            (ketBra χ η))ᴴ *
          tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂)) (ketBra χ η)) =
      (1 / 2 : ℂ) •
        ((tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
            (ketBra χ η))ᴴ *
          tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂)) (ketBra χ η)) := by
  have hcP : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))ᴴ *
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂)) =
      (1 / 2 : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂) := by
    rw [Matrix.conjTranspose_smul, proj_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, star_inv_sqrt_two_mul_self, proj_mul_proj f₁ f₂ h1 h2 h12]
  have hP : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))ᴴ *
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂)) *
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))ᴴ *
        ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))) =
      (1 / 2 : ℂ) • (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))ᴴ *
        ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))) := by
    rw [hcP, Matrix.smul_mul, Matrix.mul_smul, smul_smul, proj_mul_proj f₁ f₂ h1 h2 h12,
      smul_smul]
  rw [tensor₂_eq_kronecker,
    kronecker_conjTranspose_mul_self_sq _ _ (1 / 2) 1 hP
      (ketBra_conjTranspose_mul_self_sq χ η hχ hη), mul_one]

/-- Family I with site 2 active, singular values. -/
theorem familyI_sq_site₂ {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (f₁ f₂ : b → ℂ) (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) (h12 : braket f₁ f₂ = 0)
    (χ η : a × c → ℂ) (hχ : vecNormSq χ = 1) (hη : vecNormSq η = 1) :
    let C := (tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
      (ketBra χ η)).submatrix siteEquiv₂.symm siteEquiv₂.symm
    Cᴴ * C * (Cᴴ * C) = (1 / 2 : ℂ) • (Cᴴ * C) :=
  submatrix_conjTranspose_mul_self_sq _ siteEquiv₂.symm _ (familyI_sq f₁ f₂ h1 h2 h12 χ η hχ hη)

/-- Family I with site 3 active, singular values. -/
theorem familyI_sq_site₃ {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (f₁ f₂ : c → ℂ) (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) (h12 : braket f₁ f₂ = 0)
    (χ η : a × b → ℂ) (hχ : vecNormSq χ = 1) (hη : vecNormSq η = 1) :
    let C := (tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
      (ketBra χ η)).submatrix siteEquiv₃.symm siteEquiv₃.symm
    Cᴴ * C * (Cᴴ * C) = (1 / 2 : ℂ) • (Cᴴ * C) :=
  submatrix_conjTranspose_mul_self_sq _ siteEquiv₃.symm _ (familyI_sq f₁ f₂ h1 h2 h12 χ η hχ hη)

/-! ### The union of the three families -/

/-- The four properties asserted for the members of the union. -/
abbrev IsNormalizedHalfSingularZero
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) : Prop :=
  C.rank ≤ 2 ∧ invN C = 1 ∧ endpointEnergy C = 0 ∧
    Cᴴ * C * (Cᴴ * C) = (1 / 2 : ℂ) • (Cᴴ * C)

theorem isNormalizedHalfSingularZero_smul
    {D : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ} (z : ℂ)
    (hz : Complex.normSq z = 1) (h : IsNormalizedHalfSingularZero D) :
    IsNormalizedHalfSingularZero (z • D) := by
  obtain ⟨hr, hN, hq, hs⟩ := h
  have hzz : star z * z = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hz, Complex.ofReal_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hzD : z • D =
        (z • (1 : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)) * D := by
      rw [Matrix.smul_mul, Matrix.one_mul]
    rw [hzD]
    exact (Matrix.rank_mul_le_right _ _).trans hr
  · unfold invN at hN ⊢
    rw [frobSq_smul, hz, one_mul, hN]
  · unfold endpointEnergy at hq ⊢
    rw [energy_smul, hz, one_mul, hq]
  · have hC : (z • D)ᴴ * (z • D) = Dᴴ * D := by
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hzz, one_smul]
    rw [hC, hs]

/-- Theorem 5.1, inclusion "⊇", for the whole union: every member is a normalized complex
27 × 27 matrix of rank at most two with endpoint energy zero whose two nonzero singular values
both equal `1/√2`.  (The converse inclusion is the open classification `T5.1`.) -/
theorem isNormalizedHalfSingularZero_of_isQutritZeroFamilyMember
    {C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ}
    (hC : IsQutritZeroFamilyMember C) : IsNormalizedHalfSingularZero C := by
  obtain ⟨z, hz, D, rfl, hD⟩ := hC
  refine isNormalizedHalfSingularZero_smul z hz ?_
  rcases hD with ⟨f₁, f₂, χ, η, h1, h2, h12, hχ, hη, hD⟩ |
      ⟨a, b, U, V₂, V₃, ha, hb, hU, h₂, h₃, hD⟩ | ⟨U, V₁, V₂, V₃, hU, h₁, h₂, h₃, rfl⟩
  · rcases hD with rfl | rfl | rfl
    · obtain ⟨hr, hN, hq⟩ := familyI_endpoint_zero_general f₁ f₂ h1 h2 h12 χ η hχ hη
      exact ⟨hr, hN, hq, familyI_sq f₁ f₂ h1 h2 h12 χ η hχ hη⟩
    · obtain ⟨hr, hN, hq⟩ := familyI_endpoint_zero_site₂ f₁ f₂ h1 h2 h12 χ η hχ hη
      exact ⟨hr, hN, hq, familyI_sq_site₂ f₁ f₂ h1 h2 h12 χ η hχ hη⟩
    · obtain ⟨hr, hN, hq⟩ := familyI_endpoint_zero_site₃ f₁ f₂ h1 h2 h12 χ η hχ hη
      exact ⟨hr, hN, hq, familyI_sq_site₃ f₁ f₂ h1 h2 h12 χ η hχ hη⟩
  · rcases hD with rfl | rfl | rfl
    · obtain ⟨hr, hN, hq⟩ := familyII_endpoint_zero a b ha hb U hU V₂ V₃ h₂ h₃
      exact ⟨hr, hN, hq, familyII_sq a b ha hb U hU V₂ V₃ h₂ h₃⟩
    · exact familyII_endpoint_zero_site₂ a b ha hb U hU V₂ V₃ h₂ h₃
    · exact familyII_endpoint_zero_site₃ a b ha hb U hU V₂ V₃ h₂ h₃
  · exact familyIII_endpoint_zero U hU V₁ V₂ V₃ h₁ h₂ h₃

end ThreeCopyQutritWerner

end
