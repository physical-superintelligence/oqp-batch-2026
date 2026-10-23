module

public import ThreeCopyQutritWerner.CertificateTensorRealization
public import ThreeCopyQutritWerner.CertificateSiteRegroup

@[expose] public section


/-!
# Positive realizations on the manuscript's six physical registers

The three-site complete basis is transferred back through the literal physical
register equivalence. These existence theorems take arbitrary joint blocks
positive in their original metrics. They do not assert the endpoint identity,
carrier support, repair margins, or the existence of particular numerical blocks.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- Return from the archive's site ordering to the statement's six-register ordering. -/
def certificateUngroupMatrix
    (M : Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord) ℂ) :
    Matrix SixRegisters SixRegisters ℂ :=
  M.submatrix certificateSiteRegroupEquiv certificateSiteRegroupEquiv

theorem certificateRegroupMatrix_ungroup
    (M : Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord) ℂ) :
    certificateRegroupMatrix (certificateUngroupMatrix M) = M := by
  ext i j
  simp [certificateRegroupMatrix, certificateUngroupMatrix, Matrix.submatrix_apply]

theorem certificateUngroupMatrix_posSemidef
    (M : Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord) ℂ)
    (hM : M.PosSemidef) : (certificateUngroupMatrix M).PosSemidef :=
  hM.submatrix certificateSiteRegroupEquiv

/-- Actual six-register positivity and the prescribed joint coefficient action in sector 0. -/
theorem certificateGlobalRealization0
    (A : (t : Fin 7 × Fin 7 × Fin 7) →
      Matrix (Fin (certificateThreeSiteFrameSystem0.size t))
        (Fin (certificateThreeSiteFrameSystem0.size t)) ℂ)
    (hA : ∀ t, (certificateThreeSiteFrameSystem0.metric t * A t).PosSemidef) :
    ∃ M : Matrix SixRegisters SixRegisters ℂ, M.PosSemidef ∧
      certificateRegroupMatrix M * certificateThreeSiteFrameSystem0.basis =
        certificateThreeSiteFrameSystem0.basis *
          Matrix.blockDiagonal' (fun f => A (certificateThreeSiteFrameSystem0.type f)) := by
  obtain ⟨N, hN, hNA⟩ := certificateThreeSiteFrameSystem0_realize A hA
  refine ⟨certificateUngroupMatrix N, certificateUngroupMatrix_posSemidef N hN, ?_⟩
  rwa [certificateRegroupMatrix_ungroup]

/-- Actual six-register positivity and the prescribed joint coefficient action in sector 1. -/
theorem certificateGlobalRealization1
    (A : (t : Fin 8 × Fin 8 × Fin 8) →
      Matrix (Fin (certificateThreeSiteFrameSystem1.size t))
        (Fin (certificateThreeSiteFrameSystem1.size t)) ℂ)
    (hA : ∀ t, (certificateThreeSiteFrameSystem1.metric t * A t).PosSemidef) :
    ∃ M : Matrix SixRegisters SixRegisters ℂ, M.PosSemidef ∧
      certificateRegroupMatrix M * certificateThreeSiteFrameSystem1.basis =
        certificateThreeSiteFrameSystem1.basis *
          Matrix.blockDiagonal' (fun f => A (certificateThreeSiteFrameSystem1.type f)) := by
  obtain ⟨N, hN, hNA⟩ := certificateThreeSiteFrameSystem1_realize A hA
  refine ⟨certificateUngroupMatrix N, certificateUngroupMatrix_posSemidef N hN, ?_⟩
  rwa [certificateRegroupMatrix_ungroup]

/-- Actual six-register positivity and the prescribed joint coefficient action in sector 2. -/
theorem certificateGlobalRealization2
    (A : (t : Fin 7 × Fin 7 × Fin 7) →
      Matrix (Fin (certificateThreeSiteFrameSystem2.size t))
        (Fin (certificateThreeSiteFrameSystem2.size t)) ℂ)
    (hA : ∀ t, (certificateThreeSiteFrameSystem2.metric t * A t).PosSemidef) :
    ∃ M : Matrix SixRegisters SixRegisters ℂ, M.PosSemidef ∧
      certificateRegroupMatrix M * certificateThreeSiteFrameSystem2.basis =
        certificateThreeSiteFrameSystem2.basis *
          Matrix.blockDiagonal' (fun f => A (certificateThreeSiteFrameSystem2.type f)) := by
  obtain ⟨N, hN, hNA⟩ := certificateThreeSiteFrameSystem2_realize A hA
  refine ⟨certificateUngroupMatrix N, certificateUngroupMatrix_posSemidef N hN, ?_⟩
  rwa [certificateRegroupMatrix_ungroup]

end ThreeCopyQutritWerner
