module

public import ThreeCopyQutritWerner.CertificateTensorActions
public import ThreeCopyQutritWerner.CertificateGlobalRealization

@[expose] public section


/-!
# Finite global diagram combinations on the original physical registers

Each term may use independent local coefficients. Summing these tensor terms
therefore includes arbitrary correlated three-site diagram coefficients. The
physical operator is defined on the manuscript's six registers; the source
actions use the unchanged original row-major tensor coordinates.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Weighted finite sums commute with the literal dependent block construction. -/
theorem certificate_blockDiagonal_weighted_sum
    {ι F : Type*} [Fintype ι] [DecidableEq F] (size : F → ℕ)
    (w : ι → ℂ)
    (A : (i : ι) → (f : F) → Matrix (Fin (size f)) (Fin (size f)) ℂ) :
    Matrix.blockDiagonal' (fun f => ∑ i, w i • A i f) =
      ∑ i, w i • Matrix.blockDiagonal' (A i) := by
  ext ⟨f, r⟩ ⟨g, c⟩
  by_cases h : f = g
  · subst g
    simp only [Matrix.blockDiagonal'_apply_eq, Matrix.sum_apply, Matrix.smul_apply]
  · simp [Matrix.blockDiagonal'_apply, Matrix.sum_apply, Matrix.smul_apply, h]

/-- Exact physical intertwining is linear in the actual operator and its source action. -/
theorem certificatePhysicalFrameSystem_intertwines_sum
    {ι n F T : Type*} [Fintype ι] [Fintype n] [Fintype F]
    [DecidableEq F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T)
    (w : ι → ℂ) (M : ι → Matrix n n ℂ)
    (A : (i : ι) → (t : T) → Matrix (Fin (s.size t)) (Fin (s.size t)) ℂ)
    (h : ∀ i, M i * s.basis = s.basis *
      Matrix.blockDiagonal' (fun f => A i (s.type f))) :
    (∑ i, w i • M i) * s.basis = s.basis *
      Matrix.blockDiagonal' (fun f => ∑ i, w i • A i (s.type f)) := by
  rw [certificate_blockDiagonal_weighted_sum, Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.smul_mul, Matrix.mul_smul, h i]

/-- An arbitrary finite combination of physical three-site diagram tensor terms. -/
def certificateGlobalDiagramCombination {ι : Type*} [Fintype ι]
    (S : Finset (Fin 6)) (w : ι → ℂ)
    (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ) :
    Matrix SixRegisters SixRegisters ℂ :=
  certificateUngroupMatrix (∑ i, w i •
    (certificateLocalDiagramCombination S (w₁ i) ⊗ₖ
      (certificateLocalDiagramCombination S (w₂ i) ⊗ₖ
        certificateLocalDiagramCombination S (w₃ i))))

/-- Regrouping exposes exactly the specified physical tensor terms. -/
theorem certificateGlobalDiagramCombination_regroup {ι : Type*} [Fintype ι]
    (S : Finset (Fin 6)) (w : ι → ℂ)
    (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ) :
    certificateRegroupMatrix (certificateGlobalDiagramCombination S w w₁ w₂ w₃) =
      ∑ i, w i • (certificateLocalDiagramCombination S (w₁ i) ⊗ₖ
        (certificateLocalDiagramCombination S (w₂ i) ⊗ₖ
          certificateLocalDiagramCombination S (w₃ i))) :=
  certificateRegroupMatrix_ungroup _

/-- No source-action premise remains for an arbitrary finite global combination in sector 0. -/
theorem certificateGlobalDiagramActions0 {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ) :
    certificateRegroupMatrix (certificateGlobalDiagramCombination {5} w w₁ w₂ w₃) *
      certificateThreeSiteFrameSystem0.basis = certificateThreeSiteFrameSystem0.basis *
        Matrix.blockDiagonal' (fun f => ∑ i, w i •
          certificateTripleSourceAction certificatePhysicalFrameSystem0
            (certificateLocalDecomposition0Action (w₁ i))
            (certificateLocalDecomposition0Action (w₂ i))
            (certificateLocalDecomposition0Action (w₃ i))
            (certificateThreeSiteFrameSystem0.type f)) := by
  rw [certificateGlobalDiagramCombination_regroup]
  exact certificatePhysicalFrameSystem_intertwines_sum certificateThreeSiteFrameSystem0
    w _ _ (fun i => certificateThreeSiteDiagramActions0 (w₁ i) (w₂ i) (w₃ i))

/-- The corresponding exact action in sector 1, with its actual PT convention. -/
theorem certificateGlobalDiagramActions1 {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ) :
    certificateRegroupMatrix (certificateGlobalDiagramCombination {3, 4, 5} w w₁ w₂ w₃) *
      certificateThreeSiteFrameSystem1.basis = certificateThreeSiteFrameSystem1.basis *
        Matrix.blockDiagonal' (fun f => ∑ i, w i •
          certificateTripleSourceAction certificatePhysicalFrameSystem1
            (certificateLocalDecomposition1Action (w₁ i))
            (certificateLocalDecomposition1Action (w₂ i))
            (certificateLocalDecomposition1Action (w₃ i))
            (certificateThreeSiteFrameSystem1.type f)) := by
  rw [certificateGlobalDiagramCombination_regroup]
  exact certificatePhysicalFrameSystem_intertwines_sum certificateThreeSiteFrameSystem1
    w _ _ (fun i => certificateThreeSiteDiagramActions1 (w₁ i) (w₂ i) (w₃ i))

/-- The corresponding exact action in sector 2, with its actual PT convention. -/
theorem certificateGlobalDiagramActions2 {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (w₁ w₂ w₃ : ι → Equiv.Perm (Fin 6) → ℂ) :
    certificateRegroupMatrix (certificateGlobalDiagramCombination {1, 2, 3, 4, 5} w w₁ w₂ w₃) *
      certificateThreeSiteFrameSystem2.basis = certificateThreeSiteFrameSystem2.basis *
        Matrix.blockDiagonal' (fun f => ∑ i, w i •
          certificateTripleSourceAction certificatePhysicalFrameSystem2
            (certificateLocalDecomposition2Action (w₁ i))
            (certificateLocalDecomposition2Action (w₂ i))
            (certificateLocalDecomposition2Action (w₃ i))
            (certificateThreeSiteFrameSystem2.type f)) := by
  rw [certificateGlobalDiagramCombination_regroup]
  exact certificatePhysicalFrameSystem_intertwines_sum certificateThreeSiteFrameSystem2
    w _ _ (fun i => certificateThreeSiteDiagramActions2 (w₁ i) (w₂ i) (w₃ i))

end ThreeCopyQutritWerner
