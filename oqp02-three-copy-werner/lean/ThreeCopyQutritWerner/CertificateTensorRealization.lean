module

public import ThreeCopyQutritWerner.CertificateTensorFrame
public import ThreeCopyQutritWerner.CertificateLocalRealization

@[expose] public section


/-!
# Actual three-site positive block realizations

This proof bundle records a fully established physical frame system. Each of the
three concrete systems below supplies every field from literal archive data and
proved physical identities. Tensoring preserves those proofs and permits arbitrary
joint coefficient blocks; no factorization of the proposed blocks is required.
-/

noncomputable section

open scoped Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-- An exact complete physical basis with its unchanged source and scalar metrics. -/
structure CertificatePhysicalFrameSystem (n F T : Type*)
    [Fintype n] [Fintype F] [DecidableEq T] where
  size : T → ℕ
  type : F → T
  pivot : (t : T) → Fin (size t)
  basis : Matrix n (Σ f, Fin (size (type f))) ℂ
  metric : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ
  scalar : Matrix F F ℂ
  basis_bijective : Function.Bijective basis.mulVec
  metric_posDef : ∀ t, (metric t).PosDef
  gram : basisᴴ * basis = certificateRepeatedFrameMetric size type metric scalar
  scalar_off_type : ∀ f g, type f ≠ type g → scalar f g = 0

/-- Tensor product of two established physical systems, with exact finite regrouping. -/
@[reducible] def certificatePhysicalFrameTensor
    {n₁ n₂ F₁ F₂ T₁ T₂ : Type*}
    [Fintype n₁] [Fintype n₂] [Fintype F₁] [Fintype F₂]
    [DecidableEq n₁] [DecidableEq n₂] [DecidableEq F₁] [DecidableEq F₂]
    [DecidableEq T₁] [DecidableEq T₂]
    (a : CertificatePhysicalFrameSystem n₁ F₁ T₁)
    (b : CertificatePhysicalFrameSystem n₂ F₂ T₂) :
    CertificatePhysicalFrameSystem (n₁ × n₂) (F₁ × F₂) (T₁ × T₂) where
  size t := a.size t.1 * b.size t.2
  type f := (a.type f.1, b.type f.2)
  pivot t := finProdFinEquiv (a.pivot t.1, b.pivot t.2)
  basis := (a.basis ⊗ₖ b.basis).submatrix id
    (certificateTensorFrameIndex a.size b.size a.type b.type)
  metric := certificateTensorSourceGram a.size b.size a.metric b.metric
  scalar := a.scalar ⊗ₖ b.scalar
  basis_bijective := certificateTensorFrame_bijective a.size b.size a.type b.type
    a.basis b.basis a.basis_bijective b.basis_bijective
  metric_posDef := certificateTensorSourceGram_posDef a.size b.size a.metric b.metric
    a.metric_posDef b.metric_posDef
  gram := certificateTensorFrame_gram a.size b.size a.type b.type a.basis b.basis
    a.metric b.metric a.scalar b.scalar a.gram b.gram
  scalar_off_type := by
    intro f g hfg
    by_cases ha : a.type f.1 = a.type g.1
    · have hb : b.type f.2 ≠ b.type g.2 := fun h => hfg (Prod.ext ha h)
      simp only [Matrix.kroneckerMap_apply, b.scalar_off_type _ _ hb, mul_zero]
    · simp only [Matrix.kroneckerMap_apply, a.scalar_off_type _ _ ha, zero_mul]

/-- A proved physical system realizes arbitrary positive blocks in its original metric. -/
theorem certificatePhysicalFrameSystem_realize
    {n F T : Type*} [Fintype n] [Fintype F] [Fintype T]
    [DecidableEq n] [DecidableEq F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T)
    (A : (t : T) → Matrix (Fin (s.size t)) (Fin (s.size t)) ℂ)
    (hA : ∀ t, (s.metric t * A t).PosSemidef) :
    ∃ M : Matrix n n ℂ, M.PosSemidef ∧
      M * s.basis = s.basis * Matrix.blockDiagonal' (fun f => A (s.type f)) :=
  certificate_exists_positive_frame_realization s.size s.type s.pivot s.basis
    s.metric A s.scalar s.basis_bijective s.metric_posDef s.gram s.scalar_off_type hA

/-- The concrete archive sector 0; every physical and metric field is proved. -/
@[reducible] def certificatePhysicalFrameSystem0 :
    CertificatePhysicalFrameSystem CertificateLocalWord (Fin 153) (Fin 7) where
  size := certificateDescendantFrames2SourceSize
  type := certificateDescendantFrames2Type
  pivot t := ⟨0, certificateLocalRealization0size_pos t⟩
  basis := certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ)
  metric := certificateLocalDecomposition0Gram
  scalar := certificateDescendantGram2K.map (Int.cast : ℤ → ℂ)
  basis_bijective := certificateDescendantFrames0Matrix_complex_bijective
  metric_posDef := certificateLocalDecomposition0Gram_posDef
  gram := certificateLocalRealization0gram
  scalar_off_type := by
    intro f g hfg
    change (certificateDescendantGram2K f g : ℂ) = 0
    rw [certificateDescendantGram2K_off_type f g hfg, Int.cast_zero]

/-- All three actual physical sites in sector 0, in right-associated row-major order. -/
@[reducible] def certificateThreeSiteFrameSystem0 :
    CertificatePhysicalFrameSystem
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (Fin 153 × Fin 153 × Fin 153) (Fin 7 × Fin 7 × Fin 7) :=
  certificatePhysicalFrameTensor certificatePhysicalFrameSystem0
    (certificatePhysicalFrameTensor certificatePhysicalFrameSystem0 certificatePhysicalFrameSystem0)

/-- Every positive joint original-metric tuple produces a positive operator on the
actual three-site physical space. The coefficient blocks may be arbitrary. -/
theorem certificateThreeSiteFrameSystem0_realize
    (A : (t : Fin 7 × Fin 7 × Fin 7) →
      Matrix (Fin (certificateThreeSiteFrameSystem0.size t))
        (Fin (certificateThreeSiteFrameSystem0.size t)) ℂ)
    (hA : ∀ t, (certificateThreeSiteFrameSystem0.metric t * A t).PosSemidef) :
    ∃ M : Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord) ℂ,
      M.PosSemidef ∧ M * certificateThreeSiteFrameSystem0.basis =
        certificateThreeSiteFrameSystem0.basis *
          Matrix.blockDiagonal' (fun f => A (certificateThreeSiteFrameSystem0.type f)) :=
  certificatePhysicalFrameSystem_realize certificateThreeSiteFrameSystem0 A hA

/-- The concrete archive sector 1; every physical and metric field is proved. -/
@[reducible] def certificatePhysicalFrameSystem1 :
    CertificatePhysicalFrameSystem CertificateLocalWord (Fin 190) (Fin 8) where
  size := certificateDescendantFrames1SourceSize
  type := certificateDescendantFrames1Type
  pivot t := ⟨0, certificateLocalRealization1size_pos t⟩
  basis := certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ)
  metric := certificateLocalDecomposition1Gram
  scalar := certificateDescendantGram1K.map (Int.cast : ℤ → ℂ)
  basis_bijective := certificateDescendantFrames1Matrix_complex_bijective
  metric_posDef := certificateLocalDecomposition1Gram_posDef
  gram := certificateLocalRealization1gram
  scalar_off_type := by
    intro f g hfg
    change (certificateDescendantGram1K f g : ℂ) = 0
    rw [certificateDescendantGram1K_off_type f g hfg, Int.cast_zero]

/-- All three actual physical sites in sector 1, in right-associated row-major order. -/
@[reducible] def certificateThreeSiteFrameSystem1 :
    CertificatePhysicalFrameSystem
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (Fin 190 × Fin 190 × Fin 190) (Fin 8 × Fin 8 × Fin 8) :=
  certificatePhysicalFrameTensor certificatePhysicalFrameSystem1
    (certificatePhysicalFrameTensor certificatePhysicalFrameSystem1 certificatePhysicalFrameSystem1)

/-- Every positive joint original-metric tuple produces a positive operator on the
actual three-site physical space. The coefficient blocks may be arbitrary. -/
theorem certificateThreeSiteFrameSystem1_realize
    (A : (t : Fin 8 × Fin 8 × Fin 8) →
      Matrix (Fin (certificateThreeSiteFrameSystem1.size t))
        (Fin (certificateThreeSiteFrameSystem1.size t)) ℂ)
    (hA : ∀ t, (certificateThreeSiteFrameSystem1.metric t * A t).PosSemidef) :
    ∃ M : Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord) ℂ,
      M.PosSemidef ∧ M * certificateThreeSiteFrameSystem1.basis =
        certificateThreeSiteFrameSystem1.basis *
          Matrix.blockDiagonal' (fun f => A (certificateThreeSiteFrameSystem1.type f)) :=
  certificatePhysicalFrameSystem_realize certificateThreeSiteFrameSystem1 A hA

/-- The concrete archive sector 2; every physical and metric field is proved. -/
@[reducible] def certificatePhysicalFrameSystem2 :
    CertificatePhysicalFrameSystem CertificateLocalWord (Fin 153) (Fin 7) where
  size := certificateDescendantFrames2SourceSize
  type := certificateDescendantFrames2Type
  pivot t := ⟨0, certificateLocalRealization2size_pos t⟩
  basis := certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ)
  metric := certificateLocalDecomposition2Gram
  scalar := certificateDescendantGram2K.map (Int.cast : ℤ → ℂ)
  basis_bijective := certificateDescendantFrames2Matrix_complex_bijective
  metric_posDef := certificateLocalDecomposition2Gram_posDef
  gram := certificateLocalRealization2gram
  scalar_off_type := by
    intro f g hfg
    change (certificateDescendantGram2K f g : ℂ) = 0
    rw [certificateDescendantGram2K_off_type f g hfg, Int.cast_zero]

/-- All three actual physical sites in sector 2, in right-associated row-major order. -/
@[reducible] def certificateThreeSiteFrameSystem2 :
    CertificatePhysicalFrameSystem
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (Fin 153 × Fin 153 × Fin 153) (Fin 7 × Fin 7 × Fin 7) :=
  certificatePhysicalFrameTensor certificatePhysicalFrameSystem2
    (certificatePhysicalFrameTensor certificatePhysicalFrameSystem2 certificatePhysicalFrameSystem2)

/-- Every positive joint original-metric tuple produces a positive operator on the
actual three-site physical space. The coefficient blocks may be arbitrary. -/
theorem certificateThreeSiteFrameSystem2_realize
    (A : (t : Fin 7 × Fin 7 × Fin 7) →
      Matrix (Fin (certificateThreeSiteFrameSystem2.size t))
        (Fin (certificateThreeSiteFrameSystem2.size t)) ℂ)
    (hA : ∀ t, (certificateThreeSiteFrameSystem2.metric t * A t).PosSemidef) :
    ∃ M : Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord) ℂ,
      M.PosSemidef ∧ M * certificateThreeSiteFrameSystem2.basis =
        certificateThreeSiteFrameSystem2.basis *
          Matrix.blockDiagonal' (fun f => A (certificateThreeSiteFrameSystem2.type f)) :=
  certificatePhysicalFrameSystem_realize certificateThreeSiteFrameSystem2 A hA

end ThreeCopyQutritWerner
