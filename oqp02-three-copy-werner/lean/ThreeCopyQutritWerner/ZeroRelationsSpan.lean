module

public import ThreeCopyQutritWerner.ZeroRelationsFamilies

@[expose] public section


/-!
# Fixed linear feature maps for equation (24)

The contraction of `z_h = vec C ⊗ p ⊗ p` defined here equals `H(C,p) ⊗ p`.
Applying the appropriate local antisymmetrizers to its two pairs gives three fixed complex
linear maps whose values are exactly the three left sides of manuscript eq. (24).
They annihilate the span of all known zero features.

The final implication from membership in that span to the zero relations is unconditional
linear algebra. Proving that an arbitrary endpoint zero has its feature in this span remains
the separate, open saturated-kernel certificate claim S5.1-kernel.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

section LinearMaps

variable {n : Type*} [Fintype n]

/-- Two matrix factors, regarded as a four-register vector. -/
def pairProduct (H P : Matrix n n ℂ) : ((n × n) × (n × n)) → ℂ :=
  fun q => H q.1.1 q.1.2 * P q.2.1 q.2.2

/-- Contract one row/column register with the first minor pair. On `vec C ⊗ p ⊗ p`,
this is `H(C,p) ⊗ p`; all transposes are plain transposes. -/
def featureHContraction :
    (((n × n) × (n × n)) × (n × n) → ℂ) →ₗ[ℂ] (((n × n) × (n × n)) → ℂ) where
  toFun f q := (∑ t, (f (((q.1.1, t), (t, q.1.2)), q.2) -
    f (((q.1.2, t), (q.1.1, t)), q.2))) / 2
  map_add' f g := by
    ext q
    simp only [Pi.add_apply]
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    ring
  map_smul' z f := by
    ext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← mul_sub,
      ← Finset.mul_sum, mul_div_assoc]

/-- Antisymmetrize the first physical pair in a four-register vector. -/
def pairAntiLeft (e : n × n ≃ n × n) :
    (((n × n) × (n × n)) → ℂ) →ₗ[ℂ] (((n × n) × (n × n)) → ℂ) where
  toFun f q := (f q - f (e q.1, q.2)) / 2
  map_add' f g := by ext q; simp only [Pi.add_apply]; ring
  map_smul' z f := by
    ext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Antisymmetrize the second physical pair in a four-register vector. -/
def pairAntiRight (e : n × n ≃ n × n) :
    (((n × n) × (n × n)) → ℂ) →ₗ[ℂ] (((n × n) × (n × n)) → ℂ) where
  toFun f q := (f q - f (q.1, e q.2)) / 2
  map_add' f g := by ext q; simp only [Pi.add_apply]; ring
  map_smul' z f := by
    ext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The matrix form of antisymmetrization by a pair-index equivalence. -/
def pairAntiMatrix (e : n × n ≃ n × n) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  fun r s => (M r s - M (e (r, s)).1 (e (r, s)).2) / 2

theorem pairAntiLeft_pairProduct (e : n × n ≃ n × n) (H P : Matrix n n ℂ) :
    pairAntiLeft e (pairProduct H P) = pairProduct (pairAntiMatrix e H) P := by
  ext q
  change (H q.1.1 q.1.2 * P q.2.1 q.2.2 -
    H (e q.1).1 (e q.1).2 * P q.2.1 q.2.2) / 2 =
    ((H q.1.1 q.1.2 - H (e q.1).1 (e q.1).2) / 2) * P q.2.1 q.2.2
  ring

theorem pairAntiRight_pairProduct (e : n × n ≃ n × n) (H P : Matrix n n ℂ) :
    pairAntiRight e (pairProduct H P) = pairProduct H (pairAntiMatrix e P) := by
  ext q
  change (H q.1.1 q.1.2 * P q.2.1 q.2.2 -
    H q.1.1 q.1.2 * P (e q.2).1 (e q.2).2) / 2 =
    H q.1.1 q.1.2 * ((P q.2.1 q.2.2 - P (e q.2).1 (e q.2).2) / 2)
  ring

end LinearMaps

/-- The four physical registers left after the contraction, grouped as two pairs. -/
abbrev FourRegisters :=
  ((Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3)) ×
    ((Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3))

/-- The contraction evaluates to the tensor in (24) before its local antisymmetrizers. -/
theorem featureHContraction_featureH
    (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    featureHContraction (featureH C P) = pairProduct (hFeature C P) P := by
  ext q
  change (∑ t, (C q.1.1 t * P t q.1.2 * P q.2.1 q.2.2 -
      C q.1.2 t * P q.1.1 t * P q.2.1 q.2.2)) / 2 =
    (1 / 2 * ((∑ t, C q.1.1 t * P t q.1.2) -
      ∑ t, P q.1.1 t * C q.1.2 t)) * P q.2.1 q.2.2
  have hs : (∑ t, (C q.1.1 t * P t q.1.2 * P q.2.1 q.2.2 -
      C q.1.2 t * P q.1.1 t * P q.2.1 q.2.2)) =
      ∑ t, (C q.1.1 t * P t q.1.2 - P q.1.1 t * C q.1.2 t) * P q.2.1 q.2.2 := by
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hs, ← Finset.sum_mul, Finset.sum_sub_distrib]
  ring

/-- The fixed linear map giving `(A₂A₃H) ⊗ (A₁p)`. -/
def zeroRelationMap₁ : (SixRegisters → ℂ) →ₗ[ℂ] (FourRegisters → ℂ) :=
  (pairAntiRight siteSwap₁).comp
    ((pairAntiLeft siteSwap₂).comp ((pairAntiLeft siteSwap₃).comp featureHContraction))

/-- The fixed linear map giving `(A₁A₃H) ⊗ (A₂p)`. -/
def zeroRelationMap₂ : (SixRegisters → ℂ) →ₗ[ℂ] (FourRegisters → ℂ) :=
  (pairAntiRight siteSwap₂).comp
    ((pairAntiLeft siteSwap₁).comp ((pairAntiLeft siteSwap₃).comp featureHContraction))

/-- The fixed linear map giving `(A₁A₂H) ⊗ (A₃p)`. -/
def zeroRelationMap₃ : (SixRegisters → ℂ) →ₗ[ℂ] (FourRegisters → ℂ) :=
  (pairAntiRight siteSwap₃).comp
    ((pairAntiLeft siteSwap₁).comp ((pairAntiLeft siteSwap₂).comp featureHContraction))

theorem zeroRelationMap₁_featureH
    (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    zeroRelationMap₁ (featureH C P) =
      pairProduct (siteAnti₂ (siteAnti₃ (hFeature C P))) (siteAnti₁ P) := by
  simp only [zeroRelationMap₁, LinearMap.comp_apply, featureHContraction_featureH,
    pairAntiLeft_pairProduct, pairAntiRight_pairProduct]
  rfl

theorem zeroRelationMap₂_featureH
    (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    zeroRelationMap₂ (featureH C P) =
      pairProduct (siteAnti₁ (siteAnti₃ (hFeature C P))) (siteAnti₂ P) := by
  simp only [zeroRelationMap₂, LinearMap.comp_apply, featureHContraction_featureH,
    pairAntiLeft_pairProduct, pairAntiRight_pairProduct]
  rfl

theorem zeroRelationMap₃_featureH
    (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    zeroRelationMap₃ (featureH C P) =
      pairProduct (siteAnti₁ (siteAnti₂ (hFeature C P))) (siteAnti₃ P) := by
  simp only [zeroRelationMap₃, LinearMap.comp_apply, featureHContraction_featureH,
    pairAntiLeft_pairProduct, pairAntiRight_pairProduct]
  rfl

/-- Eq. (24) is exactly vanishing of the three fixed linear maps on `z_h`. -/
theorem zeroRelations_iff_featureH_maps_eq_zero
    (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    ZeroRelations (hFeature C P) P ↔
      zeroRelationMap₁ (featureH C P) = 0 ∧ zeroRelationMap₂ (featureH C P) = 0 ∧
        zeroRelationMap₃ (featureH C P) = 0 := by
  rw [zeroRelationMap₁_featureH, zeroRelationMap₂_featureH, zeroRelationMap₃_featureH]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · funext q
      exact h.1 q.1.1 q.1.2 q.2.1 q.2.2
    · funext q
      exact h.2.1 q.1.1 q.1.2 q.2.1 q.2.2
    · funext q
      exact h.2.2 q.1.1 q.1.2 q.2.1 q.2.2
  · intro h
    exact ⟨fun r s r' s' => congrFun h.1 ((r, s), (r', s')),
      fun r s r' s' => congrFun h.2.1 ((r, s), (r', s')),
      fun r s r' s' => congrFun h.2.2 ((r, s), (r', s'))⟩

/-- Holomorphic features of normalized members of the known union, allowing every width-two
factorization. This set is defined directly from the known families, without endpoint
classification or a certificate-kernel assumption. -/
def knownZeroFeatures : Set (SixRegisters → ℂ) :=
  {v | ∃ (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
      (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
      (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ),
    IsQutritZeroFamilyMember C ∧ C = X * B ∧ v = featureH C (bivecMat X)}

/-- The span of known features allowing every width-two source factorization. Its equality
with the span using orthonormal source columns is proved below. -/
def knownZeroFeatureSpan : Submodule ℂ (SixRegisters → ℂ) :=
  Submodule.span ℂ knownZeroFeatures

/-- Changing the two source columns by a `2 × 2` matrix multiplies their bivector by its
explicit determinant. -/
theorem bivecMat_mul_two {n : Type*} [Fintype n]
    (X : Matrix n (Fin 2) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    bivecMat (X * A) = (A 0 0 * A 1 1 - A 0 1 * A 1 0) • bivecMat X := by
  ext r s
  simp only [bivecMat_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- The holomorphic feature is homogeneous of degree two in its source bivector. -/
theorem featureH_smul_bivec
    (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) (z : ℂ) :
    featureH C (z • P) = z ^ 2 • featureH C P := by
  ext q
  simp only [featureH, vec, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Every width-two factorization of a rank-two matrix has its feature proportional to a
feature with orthonormal source columns. The matrix `C` is unchanged. -/
theorem exists_orthonormal_featureH_smul
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) (hr : C.rank = 2)
    (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ) (hXB : C = X * B) :
    ∃ (U : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
      (D : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ),
      Uᴴ * U = 1 ∧ C = U * D ∧
      ∃ z : ℂ, featureH C (bivecMat X) = z • featureH C (bivecMat U) := by
  obtain ⟨d, U, D, hd, hU, hUD⟩ := exists_orthonormal_mul C
  rw [hr] at hd
  subst d
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_eq_two B
    (rank_eq_two_of_mul X B (hXB ▸ hr)).2
  have hXA : X = U * (D * R) := by
    rw [← Matrix.mul_assoc, ← hUD, hXB, Matrix.mul_assoc, hR, Matrix.mul_one]
  refine ⟨U, D, hU, hUD, ((D * R) 0 0 * (D * R) 1 1 - (D * R) 0 1 * (D * R) 1 0) ^ 2, ?_⟩
  rw [hXA, bivecMat_mul_two, featureH_smul_bivec]

/-- Known zero features with orthonormal source columns, so that the source bivector has
unit norm. The normalization of `C` is still imposed by the known-family predicate. -/
def orthonormalKnownZeroFeatures : Set (SixRegisters → ℂ) :=
  {v | ∃ (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
      (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
      (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ),
    IsQutritZeroFamilyMember C ∧ Xᴴ * X = 1 ∧ C = X * B ∧ v = featureH C (bivecMat X)}

/-- Allowing arbitrary source bases does not enlarge the known-feature span relative to
orthonormal bases: change of basis merely rescales the feature by the squared determinant. -/
theorem knownZeroFeatureSpan_eq_orthonormal_span :
    knownZeroFeatureSpan = Submodule.span ℂ orthonormalKnownZeroFeatures := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨C, X, B, hC, hXB, rfl⟩ := hv
    obtain ⟨U, D, hU, hUD, z, hz⟩ := exists_orthonormal_featureH_smul C
      (rank_eq_two_of_isQutritZeroFamilyMember hC) X B hXB
    rw [hz]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨C, U, D, hC, hU, hUD, rfl⟩
  · apply Submodule.span_mono
    intro v hv
    obtain ⟨C, X, B, hC, hX, hXB, hv⟩ := hv
    exact ⟨C, X, B, hC, hXB, hv⟩

/-- Each fixed map annihilates the whole span because it annihilates every known feature. -/
theorem zeroRelationMaps_eq_zero_of_mem_knownZeroFeatureSpan (v : SixRegisters → ℂ)
    (hv : v ∈ knownZeroFeatureSpan) :
    zeroRelationMap₁ v = 0 ∧ zeroRelationMap₂ v = 0 ∧ zeroRelationMap₃ v = 0 := by
  have hle : knownZeroFeatureSpan ≤
      LinearMap.ker zeroRelationMap₁ ⊓ (LinearMap.ker zeroRelationMap₂ ⊓ LinearMap.ker zeroRelationMap₃) := by
    apply Submodule.span_le.mpr
    intro w hw
    obtain ⟨C, X, B, hC, hXB, rfl⟩ := hw
    have h := (zeroRelations_iff_featureH_maps_eq_zero C (bivecMat X)).mp
      (zeroRelations_of_isQutritZeroFamilyMember hC X B hXB)
    exact h
  exact hle hv

/-- REDUCTION: membership of an endpoint feature in the known-feature span gives (24).
Establishing this membership for arbitrary endpoint zeros is the open saturated-kernel claim. -/
theorem zeroRelations_of_mem_knownZeroFeatureSpan
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
    (hspan : featureH C (bivecMat X) ∈ knownZeroFeatureSpan) :
    ZeroRelations (hFeature C (bivecMat X)) (bivecMat X) :=
  (zeroRelations_iff_featureH_maps_eq_zero C (bivecMat X)).mpr
    (zeroRelationMaps_eq_zero_of_mem_knownZeroFeatureSpan _ hspan)

end ThreeCopyQutritWerner

end
