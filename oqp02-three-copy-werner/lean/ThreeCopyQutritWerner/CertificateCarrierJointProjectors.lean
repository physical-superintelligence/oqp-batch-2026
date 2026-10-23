module

public import ThreeCopyQutritWerner.CertificateCarrierJointActions
public import ThreeCopyQutritWerner.CertificateHighestTensor

@[expose] public section


/-!
# Actual compact carrier projections in the original tensor metrics

Rectangular tensor products of the unchanged highest frames give a faithful
source action. Their positive original Gram provides an explicit left inverse.
Thus each compact carrier action is an idempotent, selfadjoint in that original
metric, because the canonical physical carrier has those properties.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The actual mixed carrier on SixRegisters is an idempotent. -/
theorem certificateMixedQutritCarrier_idempotent :
    certificateMixedQutritCarrier * certificateMixedQutritCarrier =
      certificateMixedQutritCarrier := by
  unfold certificateMixedQutritCarrier
  rw [Matrix.submatrix_mul_equiv,
    certificateCarrierWithColumn_idempotent _ certificateMixedFiveCarrier_idempotent]

theorem certificateMixedQutritCarrier_hermitian :
    certificateMixedQutritCarrierᴴ = certificateMixedQutritCarrier := by
  simp only [certificateMixedQutritCarrier, Matrix.conjTranspose_submatrix,
    certificateCarrierWithColumn_hermitian _ certificateMixedFiveCarrier_hermitian]

/-- The actual auxiliary carrier on SixRegisters is an idempotent. -/
theorem certificateAuxiliaryQutritCarrier_idempotent :
    certificateAuxiliaryQutritCarrier * certificateAuxiliaryQutritCarrier =
      certificateAuxiliaryQutritCarrier := by
  unfold certificateAuxiliaryQutritCarrier
  rw [Matrix.submatrix_mul_equiv,
    certificateCarrierWithColumn_idempotent _ certificateAuxiliaryFiveCarrier_idempotent]

theorem certificateAuxiliaryQutritCarrier_hermitian :
    certificateAuxiliaryQutritCarrierᴴ = certificateAuxiliaryQutritCarrier := by
  simp only [certificateAuxiliaryQutritCarrier, Matrix.conjTranspose_submatrix,
    certificateCarrierWithColumn_hermitian _ certificateAuxiliaryFiveCarrier_hermitian]

/-- The physical site regrouping preserves the actual adjoint equality. -/
theorem certificateCarrier_regroup_hermitian
    (P : Matrix SixRegisters SixRegisters ℂ) (hP : Pᴴ = P) :
    (certificateRegroupMatrix P).IsHermitian := by
  change (certificateRegroupMatrix P)ᴴ = certificateRegroupMatrix P
  simp only [certificateRegroupMatrix, Matrix.conjTranspose_submatrix, hP]

/-- The original highest tensor frame for one ordered sector-0 type triple. -/
def certificateCarrierHighestTriple0 (t : Fin 7 × Fin 7 × Fin 7) :
    Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (Fin (certificatePhysicalFrameSystem0.size t.1 * (certificatePhysicalFrameSystem0.size t.2.1 * certificatePhysicalFrameSystem0.size t.2.2))) ℂ :=
  certificateTripleHighestFrame ((certificateDescendantFrames0Source t.1).map (Int.cast : ℤ → ℂ))
    ((certificateDescendantFrames0Source t.2.1).map (Int.cast : ℤ → ℂ)) ((certificateDescendantFrames0Source t.2.2).map (Int.cast : ℤ → ℂ))

/-- This frame's Gram is the exact original tensor metric, with no orthonormal replacement. -/
theorem certificateCarrierHighestTriple0_gram (t : Fin 7 × Fin 7 × Fin 7) :
    (certificateCarrierHighestTriple0 t)ᴴ * certificateCarrierHighestTriple0 t =
      certificateThreeSiteFrameSystem0.metric t := by
  unfold certificateCarrierHighestTriple0
  rw [certificateTripleHighestFrame_gram, certificateHighestSource0_gram,
    certificateHighestSource0_gram, certificateHighestSource0_gram]
  rfl

/-- The highest tensor frame has a positive definite original Gram. -/
theorem certificateCarrierHighestTriple0_gram_posDef (t : Fin 7 × Fin 7 × Fin 7) :
    ((certificateCarrierHighestTriple0 t)ᴴ * certificateCarrierHighestTriple0 t).PosDef := by
  rw [certificateCarrierHighestTriple0_gram]
  exact certificateThreeSiteFrameSystem0.metric_posDef t

/-- The canonical physical carrier acts on these unchanged original highest columns. -/
theorem certificateCarrierHighestTriple0_physical (t : Fin 7 × Fin 7 × Fin 7) :
    certificateRegroupMatrix certificateQutritCarrier * certificateCarrierHighestTriple0 t =
      certificateCarrierHighestTriple0 t * certificateCarrierJointAction0 t := by
  rw [certificateQutritCarrier_regroup_sum]
  apply certificateHighestFrame_intertwines_sum
  intro p
  exact certificateTripleHighestFrame_intertwines _ _ _ _ _ _ _ _ _
    (certificateCarrierSourceAction0_physical p t.1)
    (certificateCarrierSourceAction0_physical p t.2.1)
    (certificateCarrierSourceAction0_physical p t.2.2)

/-- No projection premise remains for the actual compact sector-0 carrier matrix. -/
theorem certificateCarrierJointAction0_idempotent (t : Fin 7 × Fin 7 × Fin 7) :
    certificateCarrierJointAction0 t * certificateCarrierJointAction0 t =
      certificateCarrierJointAction0 t := by
  apply certificateSourceFrame_projector (certificateCarrierHighestTriple0 t)
    (((certificateCarrierHighestTriple0 t)ᴴ * certificateCarrierHighestTriple0 t)⁻¹ *
      (certificateCarrierHighestTriple0 t)ᴴ)
    (certificateHighestFrame_gram_leftInverse _ (certificateCarrierHighestTriple0_gram_posDef t))
    (certificateRegroupMatrix certificateQutritCarrier) _ ?_ (certificateCarrierHighestTriple0_physical t)
  rw [← certificateRegroupMatrix_mul, certificateQutritCarrier_idempotent]

/-- The compact action is selfadjoint in the original tensor Gram, not in an assumed Euclidean metric. -/
theorem certificateCarrierJointAction0_gram_selfadjoint (t : Fin 7 × Fin 7 × Fin 7) :
    certificateThreeSiteFrameSystem0.metric t * certificateCarrierJointAction0 t =
      (certificateCarrierJointAction0 t)ᴴ * certificateThreeSiteFrameSystem0.metric t := by
  rw [← certificateCarrierHighestTriple0_gram]
  exact certificateSourceFrame_gram_selfadjoint _ _ _
    (certificateCarrier_regroup_hermitian _ certificateQutritCarrier_hermitian)
    (certificateCarrierHighestTriple0_physical t)

/-- The original highest tensor frame for one ordered sector-1 type triple. -/
def certificateCarrierHighestTriple1 (t : Fin 8 × Fin 8 × Fin 8) :
    Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (Fin (certificatePhysicalFrameSystem1.size t.1 * (certificatePhysicalFrameSystem1.size t.2.1 * certificatePhysicalFrameSystem1.size t.2.2))) ℂ :=
  certificateTripleHighestFrame ((certificateDescendantFrames1Source t.1).map (Int.cast : ℤ → ℂ))
    ((certificateDescendantFrames1Source t.2.1).map (Int.cast : ℤ → ℂ)) ((certificateDescendantFrames1Source t.2.2).map (Int.cast : ℤ → ℂ))

/-- This frame's Gram is the exact original tensor metric, with no orthonormal replacement. -/
theorem certificateCarrierHighestTriple1_gram (t : Fin 8 × Fin 8 × Fin 8) :
    (certificateCarrierHighestTriple1 t)ᴴ * certificateCarrierHighestTriple1 t =
      certificateThreeSiteFrameSystem1.metric t := by
  unfold certificateCarrierHighestTriple1
  rw [certificateTripleHighestFrame_gram, certificateHighestSource1_gram,
    certificateHighestSource1_gram, certificateHighestSource1_gram]
  rfl

/-- The highest tensor frame has a positive definite original Gram. -/
theorem certificateCarrierHighestTriple1_gram_posDef (t : Fin 8 × Fin 8 × Fin 8) :
    ((certificateCarrierHighestTriple1 t)ᴴ * certificateCarrierHighestTriple1 t).PosDef := by
  rw [certificateCarrierHighestTriple1_gram]
  exact certificateThreeSiteFrameSystem1.metric_posDef t

/-- The canonical physical carrier acts on these unchanged original highest columns. -/
theorem certificateCarrierHighestTriple1_physical (t : Fin 8 × Fin 8 × Fin 8) :
    certificateRegroupMatrix certificateMixedQutritCarrier * certificateCarrierHighestTriple1 t =
      certificateCarrierHighestTriple1 t * certificateCarrierJointAction1 t := by
  rw [certificateMixedQutritCarrier_regroup_sum]
  apply certificateHighestFrame_intertwines_sum
  intro p
  exact certificateTripleHighestFrame_intertwines _ _ _ _ _ _ _ _ _
    (certificateCarrierSourceAction1_physical p t.1)
    (certificateCarrierSourceAction1_physical p t.2.1)
    (certificateCarrierSourceAction1_physical p t.2.2)

/-- No projection premise remains for the actual compact sector-1 carrier matrix. -/
theorem certificateCarrierJointAction1_idempotent (t : Fin 8 × Fin 8 × Fin 8) :
    certificateCarrierJointAction1 t * certificateCarrierJointAction1 t =
      certificateCarrierJointAction1 t := by
  apply certificateSourceFrame_projector (certificateCarrierHighestTriple1 t)
    (((certificateCarrierHighestTriple1 t)ᴴ * certificateCarrierHighestTriple1 t)⁻¹ *
      (certificateCarrierHighestTriple1 t)ᴴ)
    (certificateHighestFrame_gram_leftInverse _ (certificateCarrierHighestTriple1_gram_posDef t))
    (certificateRegroupMatrix certificateMixedQutritCarrier) _ ?_ (certificateCarrierHighestTriple1_physical t)
  rw [← certificateRegroupMatrix_mul, certificateMixedQutritCarrier_idempotent]

/-- The compact action is selfadjoint in the original tensor Gram, not in an assumed Euclidean metric. -/
theorem certificateCarrierJointAction1_gram_selfadjoint (t : Fin 8 × Fin 8 × Fin 8) :
    certificateThreeSiteFrameSystem1.metric t * certificateCarrierJointAction1 t =
      (certificateCarrierJointAction1 t)ᴴ * certificateThreeSiteFrameSystem1.metric t := by
  rw [← certificateCarrierHighestTriple1_gram]
  exact certificateSourceFrame_gram_selfadjoint _ _ _
    (certificateCarrier_regroup_hermitian _ certificateMixedQutritCarrier_hermitian)
    (certificateCarrierHighestTriple1_physical t)

/-- The original highest tensor frame for one ordered sector-2 type triple. -/
def certificateCarrierHighestTriple2 (t : Fin 7 × Fin 7 × Fin 7) :
    Matrix (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord)
      (Fin (certificatePhysicalFrameSystem2.size t.1 * (certificatePhysicalFrameSystem2.size t.2.1 * certificatePhysicalFrameSystem2.size t.2.2))) ℂ :=
  certificateTripleHighestFrame ((certificateDescendantFrames2Source t.1).map (Int.cast : ℤ → ℂ))
    ((certificateDescendantFrames2Source t.2.1).map (Int.cast : ℤ → ℂ)) ((certificateDescendantFrames2Source t.2.2).map (Int.cast : ℤ → ℂ))

/-- This frame's Gram is the exact original tensor metric, with no orthonormal replacement. -/
theorem certificateCarrierHighestTriple2_gram (t : Fin 7 × Fin 7 × Fin 7) :
    (certificateCarrierHighestTriple2 t)ᴴ * certificateCarrierHighestTriple2 t =
      certificateThreeSiteFrameSystem2.metric t := by
  unfold certificateCarrierHighestTriple2
  rw [certificateTripleHighestFrame_gram, certificateHighestSource2_gram,
    certificateHighestSource2_gram, certificateHighestSource2_gram]
  rfl

/-- The highest tensor frame has a positive definite original Gram. -/
theorem certificateCarrierHighestTriple2_gram_posDef (t : Fin 7 × Fin 7 × Fin 7) :
    ((certificateCarrierHighestTriple2 t)ᴴ * certificateCarrierHighestTriple2 t).PosDef := by
  rw [certificateCarrierHighestTriple2_gram]
  exact certificateThreeSiteFrameSystem2.metric_posDef t

/-- The canonical physical carrier acts on these unchanged original highest columns. -/
theorem certificateCarrierHighestTriple2_physical (t : Fin 7 × Fin 7 × Fin 7) :
    certificateRegroupMatrix certificateAuxiliaryQutritCarrier * certificateCarrierHighestTriple2 t =
      certificateCarrierHighestTriple2 t * certificateCarrierJointAction2 t := by
  rw [certificateAuxiliaryQutritCarrier_regroup_sum]
  apply certificateHighestFrame_intertwines_sum
  intro p
  exact certificateTripleHighestFrame_intertwines _ _ _ _ _ _ _ _ _
    (certificateCarrierSourceAction2_physical p t.1)
    (certificateCarrierSourceAction2_physical p t.2.1)
    (certificateCarrierSourceAction2_physical p t.2.2)

/-- No projection premise remains for the actual compact sector-2 carrier matrix. -/
theorem certificateCarrierJointAction2_idempotent (t : Fin 7 × Fin 7 × Fin 7) :
    certificateCarrierJointAction2 t * certificateCarrierJointAction2 t =
      certificateCarrierJointAction2 t := by
  apply certificateSourceFrame_projector (certificateCarrierHighestTriple2 t)
    (((certificateCarrierHighestTriple2 t)ᴴ * certificateCarrierHighestTriple2 t)⁻¹ *
      (certificateCarrierHighestTriple2 t)ᴴ)
    (certificateHighestFrame_gram_leftInverse _ (certificateCarrierHighestTriple2_gram_posDef t))
    (certificateRegroupMatrix certificateAuxiliaryQutritCarrier) _ ?_ (certificateCarrierHighestTriple2_physical t)
  rw [← certificateRegroupMatrix_mul, certificateAuxiliaryQutritCarrier_idempotent]

/-- The compact action is selfadjoint in the original tensor Gram, not in an assumed Euclidean metric. -/
theorem certificateCarrierJointAction2_gram_selfadjoint (t : Fin 7 × Fin 7 × Fin 7) :
    certificateThreeSiteFrameSystem2.metric t * certificateCarrierJointAction2 t =
      (certificateCarrierJointAction2 t)ᴴ * certificateThreeSiteFrameSystem2.metric t := by
  rw [← certificateCarrierHighestTriple2_gram]
  exact certificateSourceFrame_gram_selfadjoint _ _ _
    (certificateCarrier_regroup_hermitian _ certificateAuxiliaryQutritCarrier_hermitian)
    (certificateCarrierHighestTriple2_physical t)

end ThreeCopyQutritWerner
