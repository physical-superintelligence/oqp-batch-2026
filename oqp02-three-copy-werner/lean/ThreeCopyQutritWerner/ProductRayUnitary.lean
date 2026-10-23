module

public import ThreeCopyQutritWerner.AppendixCInputs
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


/-!
# Local unitary changes of coordinates for the product-ray argument

These statements concern the literal matrix rank, endpoint energy, and reduced range
operators. No endpoint inequality or Appendix C input is assumed. The normalization
uses an orthonormal-basis extension of each nonzero local factor.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Conjugating by an isometric embedding preserves matrix rank. -/
theorem productRay_rank_conj_isometry {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (U : Matrix m n ℂ) (hU : Uᴴ * U = 1)
    (C : Matrix n n ℂ) : (U * C * Uᴴ).rank = C.rank := by
  have hrec : Uᴴ * (U * C * Uᴴ) * U = C := by
    calc
      _ = (Uᴴ * U) * C * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = C := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · calc
      C.rank = (Uᴴ * (U * C * Uᴴ) * U).rank := congrArg Matrix.rank hrec.symm
      _ ≤ (U * C * Uᴴ).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

section Invariance

variable {a b c a' b' c' : Type*} [Fintype a] [Fintype b] [Fintype c]
  [Fintype a'] [Fintype b'] [Fintype c'] [DecidableEq a] [DecidableEq b] [DecidableEq c]
  {U₁ : Matrix a' a ℂ} {U₂ : Matrix b' b ℂ} {U₃ : Matrix c' c ℂ}

/-- Rank invariance under local isometries, with the same `embed₃` as the energy theorem. -/
theorem productRay_rank_embed₃ (h₁ : U₁ᴴ * U₁ = 1) (h₂ : U₂ᴴ * U₂ = 1)
    (h₃ : U₃ᴴ * U₃ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    (embed₃ U₁ U₂ U₃ C).rank = C.rank := by
  rw [embed₃_eq_mul]
  exact productRay_rank_conj_isometry _ (kron₃_isometry h₁ h₂ h₃) C

/-- The source Gram operator transforms by the same local isometries. -/
theorem productRay_sourceGram_embed₃ (h₁ : U₁ᴴ * U₁ = 1) (h₂ : U₂ᴴ * U₂ = 1)
    (h₃ : U₃ᴴ * U₃ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    embed₃ U₁ U₂ U₃ C * (embed₃ U₁ U₂ U₃ C)ᴴ =
      embed₃ U₁ U₂ U₃ (C * Cᴴ) := by
  simp only [embed₃_eq_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [← Matrix.mul_assoc _ Cᴴ]
  exact conj_mul_conj _ (kron₃_isometry h₁ h₂ h₃) C Cᴴ

theorem productRay_localRangeDim₁_embed₃ (h₁ : U₁ᴴ * U₁ = 1) (h₂ : U₂ᴴ * U₂ = 1)
    (h₃ : U₃ᴴ * U₃ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    localRangeDim₁ (embed₃ U₁ U₂ U₃ C) = localRangeDim₁ C := by
  unfold localRangeDim₁
  rw [productRay_sourceGram_embed₃ h₁ h₂ h₃, ptrace₂₃_embed₃ h₂ h₃]
  exact productRay_rank_conj_isometry U₁ h₁ _

theorem productRay_localRangeDim₂_embed₃ (h₁ : U₁ᴴ * U₁ = 1) (h₂ : U₂ᴴ * U₂ = 1)
    (h₃ : U₃ᴴ * U₃ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    localRangeDim₂ (embed₃ U₁ U₂ U₃ C) = localRangeDim₂ C := by
  unfold localRangeDim₂
  rw [productRay_sourceGram_embed₃ h₁ h₂ h₃,
    ptrace₁₃_eq_ptrace₂₃_submatrix, embed₃_submatrix_siteEquiv₂,
    ptrace₂₃_embed₃ h₁ h₃, productRay_rank_conj_isometry U₂ h₂]
  rfl

theorem productRay_localRangeDim₃_embed₃ (h₁ : U₁ᴴ * U₁ = 1) (h₂ : U₂ᴴ * U₂ = 1)
    (h₃ : U₃ᴴ * U₃ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    localRangeDim₃ (embed₃ U₁ U₂ U₃ C) = localRangeDim₃ C := by
  unfold localRangeDim₃
  rw [productRay_sourceGram_embed₃ h₁ h₂ h₃,
    ptrace₁₂_eq_ptrace₂₃_submatrix, embed₃_submatrix_siteEquiv₃,
    ptrace₂₃_embed₃ h₁ h₂, productRay_rank_conj_isometry U₃ h₃]
  rfl

theorem productRay_endpointEnergy_embed₃ (h₁ : U₁ᴴ * U₁ = 1) (h₂ : U₂ᴴ * U₂ = 1)
    (h₃ : U₃ᴴ * U₃ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    endpointEnergy (embed₃ U₁ U₂ U₃ C) = endpointEnergy C :=
  energy_embed₃ h₁ h₂ h₃ (1 / 2) C

end Invariance

/-- A nonzero local vector can be sent to a nonzero multiple of coordinate zero by a unitary. -/
theorem productRay_exists_local_unitary (u : Fin 3 → ℂ) (hu : u ≠ 0) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℂ) (r : ℂ),
      Uᴴ * U = 1 ∧ r ≠ 0 ∧ U *ᵥ u = fun i => if i = 0 then r else 0 := by
  classical
  let x : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 u
  have hx : x ≠ 0 := by
    intro h
    apply hu
    ext i
    exact congrArg (fun y : EuclideanSpace ℂ (Fin 3) => y i) h
  let y : EuclideanSpace ℂ (Fin 3) := (‖x‖⁻¹ : ℂ) • x
  have hy : ‖y‖ = 1 := norm_smul_inv_norm hx
  have hon : Orthonormal ℂ (({0} : Set (Fin 3)).domRestrict (fun _ => y)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hy
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (ι := Fin 3) (by simp : Module.finrank ℂ (EuclideanSpace ℂ (Fin 3)) =
      Fintype.card (Fin 3)) hon
  have hb0 : b 0 = y := hb 0 (by simp)
  let a : OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)) :=
    EuclideanSpace.basisFun (Fin 3) ℂ
  let U : Matrix (Fin 3) (Fin 3) ℂ := b.toBasis.toMatrix a
  have hr : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx)
  have hxy : x = (‖x‖ : ℂ) • b 0 := by
    rw [hb0]
    change x = (‖x‖ : ℂ) • ((‖x‖ : ℂ)⁻¹ • x)
    exact (smul_inv_smul₀ hr x).symm
  refine ⟨U, (‖x‖ : ℂ), b.toMatrix_orthonormalBasis_conjTranspose_mul_self a, hr, ?_⟩
  have hrepr : U *ᵥ u = fun i => b.repr x i := by
    have h := Module.Basis.toMatrix_mulVec_repr a.toBasis b.toBasis x
    have ha : ⇑(a.toBasis.repr x) = u := by
      ext i
      rw [OrthonormalBasis.coe_toBasis_repr_apply]
      rfl
    ext i
    simpa only [U, ha, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply] using congrFun h i
  rw [hrepr]
  ext i
  conv_lhs => rw [hxy, LinearIsometryEquiv.map_smul, b.repr_self]
  simp [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, Pi.single_apply, eq_comm]

/-- Kronecker multiplication takes a product vector to the product of the local images. -/
theorem productRay_kron_mulVec (U₁ U₂ U₃ : Matrix (Fin 3) (Fin 3) ℂ)
    (u v w : Fin 3 → ℂ) :
    (U₁ ⊗ₖ (U₂ ⊗ₖ U₃)) *ᵥ (fun i => u i.1 * v i.2.1 * w i.2.2) =
      fun i => (U₁ *ᵥ u) i.1 * (U₂ *ᵥ v) i.2.1 * (U₃ *ᵥ w) i.2.2 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  calc
    _ = ∑ j, ∑ k, ∑ l,
        (U₁ i.1 j * u j) * ((U₂ i.2.1 k * v k) * (U₃ i.2.2 l * w l)) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Local unitaries take every nonzero fully product vector to the standard product ray. -/
theorem productRay_exists_product_unitaries (ψ : QutritSites → ℂ)
    (hψ : ψ ≠ 0) (hp : IsFullyProduct ψ) :
    ∃ (U₁ U₂ U₃ : Matrix (Fin 3) (Fin 3) ℂ) (r : ℂ),
      U₁ᴴ * U₁ = 1 ∧ U₂ᴴ * U₂ = 1 ∧ U₃ᴴ * U₃ = 1 ∧ r ≠ 0 ∧
      (U₁ ⊗ₖ (U₂ ⊗ₖ U₃)) *ᵥ ψ = fun i => if i = (0, 0, 0) then r else 0 := by
  classical
  obtain ⟨u, v, w, hp⟩ := hp
  have heq : ψ = fun i => u i.1 * v i.2.1 * w i.2.2 := funext hp
  have hu : u ≠ 0 := by intro h; apply hψ; ext i; simp [heq, h]
  have hv : v ≠ 0 := by intro h; apply hψ; ext i; simp [heq, h]
  have hw : w ≠ 0 := by intro h; apply hψ; ext i; simp [heq, h]
  obtain ⟨U₁, r₁, h₁, hr₁, hu'⟩ := productRay_exists_local_unitary u hu
  obtain ⟨U₂, r₂, h₂, hr₂, hv'⟩ := productRay_exists_local_unitary v hv
  obtain ⟨U₃, r₃, h₃, hr₃, hw'⟩ := productRay_exists_local_unitary w hw
  refine ⟨U₁, U₂, U₃, r₁ * r₂ * r₃, h₁, h₂, h₃,
    mul_ne_zero (mul_ne_zero hr₁ hr₂) hr₃, ?_⟩
  rw [heq, productRay_kron_mulVec, hu', hv', hw']
  ext i
  rcases i with ⟨i, j, k⟩
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> by_cases hk : k = 0 <;>
    simp [hi, hj, hk, Prod.mk.injEq]

/-- The same local conjugation puts the exact standard product vector in the matrix range.
The nonzero scalar from local normalization is absorbed into the range preimage. -/
theorem productRay_unitaries_canonical_in_range (C : Matrix QutritSites QutritSites ℂ)
    (hprod : ∃ z, C *ᵥ z ≠ 0 ∧ IsFullyProduct (C *ᵥ z)) :
    ∃ (U₁ U₂ U₃ : Matrix (Fin 3) (Fin 3) ℂ),
      U₁ᴴ * U₁ = 1 ∧ U₂ᴴ * U₂ = 1 ∧ U₃ᴴ * U₃ = 1 ∧
      ∃ z, embed₃ U₁ U₂ U₃ C *ᵥ z =
        fun i => if i = (0, 0, 0) then 1 else 0 := by
  obtain ⟨z, hz, hp⟩ := hprod
  obtain ⟨U₁, U₂, U₃, r, h₁, h₂, h₃, hr, hmap⟩ :=
    productRay_exists_product_unitaries (C *ᵥ z) hz hp
  let K := U₁ ⊗ₖ (U₂ ⊗ₖ U₃)
  have hK : Kᴴ * K = 1 := kron₃_isometry h₁ h₂ h₃
  have hcov : embed₃ U₁ U₂ U₃ C *ᵥ (K *ᵥ z) = K *ᵥ (C *ᵥ z) := by
    rw [embed₃_eq_mul]
    change (K * C * Kᴴ) *ᵥ (K *ᵥ z) = K *ᵥ (C *ᵥ z)
    simp only [Matrix.mulVec_mulVec]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [hK, Matrix.mul_one]
  refine ⟨U₁, U₂, U₃, h₁, h₂, h₃, r⁻¹ • (K *ᵥ z), ?_⟩
  rw [Matrix.mulVec_smul, hcov]
  change r⁻¹ • ((U₁ ⊗ₖ (U₂ ⊗ₖ U₃)) *ᵥ (C *ᵥ z)) = _
  rw [hmap]
  ext i
  by_cases hi : i = (0, 0, 0) <;> simp [hi, Pi.smul_apply, smul_eq_mul, hr]

end ThreeCopyQutritWerner
