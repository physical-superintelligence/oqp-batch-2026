module

public import ThreeCopyQutritWerner.CertificateCarrierPhysicalSums
public import ThreeCopyQutritWerner.CertificateCarrierSourceActions

@[expose] public section


/-!
# Exact joint carrier actions in original source coordinates

The carrier on whole physical registers is a sum over one shared permutation.
Regrouping its three sites produces one tensor cube per summand. The checked
local source actions therefore give the actual correlated joint carrier action,
with all descendant labels retained and no saved projector assumption.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Regrouping a whole-register ordinary diagram gives the same permutation at each site. -/
theorem certificateOrdinaryDiagram_three_sites (σ : Equiv.Perm (Fin 6)) :
    (certificateLocalDiagram (n := Fin 3 × Fin 3 × Fin 3) (R := ℂ) ∅ σ).submatrix
      certificateWordSiteEquiv.symm certificateWordSiteEquiv.symm =
        certificateLocalDiagram (n := Fin 3) (R := ℂ) ∅ σ ⊗ₖ
          (certificateLocalDiagram (n := Fin 3) (R := ℂ) ∅ σ ⊗ₖ
            certificateLocalDiagram (n := Fin 3) (R := ℂ) ∅ σ) := by
  simp only [certificateLocalDiagram_empty, certificatePermMatrix_prod]
  rw [certificatePermMatrix_reindex]
  apply congrArg (fun e : Equiv.Perm
    (CertificateLocalWord × CertificateLocalWord × CertificateLocalWord) => e.permMatrix ℂ)
  apply Equiv.ext
  intro r
  rfl

/-- The actual statement-base coordinate change cancels before the local-site split. -/
theorem certificateRegroupMatrix_word
    (M : Matrix (Fin 6 → Fin 3 × Fin 3 × Fin 3)
      (Fin 6 → Fin 3 × Fin 3 × Fin 3) ℂ) :
    certificateRegroupMatrix (M.submatrix certificateSixRegisterWordEquiv
      certificateSixRegisterWordEquiv) =
        M.submatrix certificateWordSiteEquiv.symm certificateWordSiteEquiv.symm := by
  ext r c
  simp [certificateRegroupMatrix, certificateSiteRegroupEquiv, Matrix.submatrix_apply]

/-- Any exact whole-register diagram sum has the corresponding correlated site expansion. -/
theorem certificateWordCarrier_regroup_sum {a : Type*} [Fintype a]
    (M : Matrix (Fin 6 → Fin 3 × Fin 3 × Fin 3)
      (Fin 6 → Fin 3 × Fin 3 × Fin 3) ℂ)
    (w : a → ℂ) (σ : a → Equiv.Perm (Fin 6))
    (hM : M = ∑ p, w p • certificateLocalDiagram (R := ℂ) ∅ (σ p)) :
    certificateRegroupMatrix (M.submatrix certificateSixRegisterWordEquiv
      certificateSixRegisterWordEquiv) =
        ∑ p, w p • (certificateLocalDiagram (n := Fin 3) (R := ℂ) ∅ (σ p) ⊗ₖ
          (certificateLocalDiagram (n := Fin 3) (R := ℂ) ∅ (σ p) ⊗ₖ
            certificateLocalDiagram (n := Fin 3) (R := ℂ) ∅ (σ p))) := by
  rw [certificateRegroupMatrix_word, hM]
  ext r c
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro p _
  exact congrArg (fun z : ℂ => w p • z)
    (congrFun (congrFun (certificateOrdinaryDiagram_three_sites (σ p)) r) c)

/-- The canonical mixed carrier on the manuscript's actual six-register space. -/
def certificateMixedQutritCarrier : Matrix SixRegisters SixRegisters ℂ :=
  (certificateCarrierWithColumn (certificateMixedFiveCarrier
    (n := Fin 3 × Fin 3 × Fin 3))).submatrix
      certificateSixRegisterWordEquiv certificateSixRegisterWordEquiv

/-- The canonical auxiliary carrier on the same actual physical space. -/
def certificateAuxiliaryQutritCarrier : Matrix SixRegisters SixRegisters ℂ :=
  (certificateCarrierWithColumn (certificateAuxiliaryFiveCarrier
    (n := Fin 3 × Fin 3 × Fin 3))).submatrix
      certificateSixRegisterWordEquiv certificateSixRegisterWordEquiv

/-- The holomorphic carrier has one shared permutation in each tensor summand. -/
theorem certificateQutritCarrier_regroup_sum :
    certificateRegroupMatrix certificateQutritCarrier =
      ∑ p : Fin 120, (certificateCarrierWeight0 p : ℂ) •
        (certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm0 p) ⊗ₖ
          (certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm0 p) ⊗ₖ
            certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm0 p))) := by
  rw [certificateQutritCarrier_eq_word_carrier]
  exact certificateWordCarrier_regroup_sum _ _ _ certificateHolomorphicSixCarrier_diagram_sum

/-- The same exact regrouping for the mixed carrier. -/
theorem certificateMixedQutritCarrier_regroup_sum :
    certificateRegroupMatrix certificateMixedQutritCarrier =
      ∑ p : Fin 12, (certificateCarrierWeight1 p : ℂ) •
        (certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm1 p) ⊗ₖ
          (certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm1 p) ⊗ₖ
            certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm1 p))) :=
  certificateWordCarrier_regroup_sum _ _ _ certificateMixedSixCarrier_diagram_sum

/-- The same exact regrouping for the auxiliary carrier. -/
theorem certificateAuxiliaryQutritCarrier_regroup_sum :
    certificateRegroupMatrix certificateAuxiliaryQutritCarrier =
      ∑ p : Fin 24, (certificateCarrierWeight2 p : ℂ) •
        (certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm2 p) ⊗ₖ
          (certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm2 p) ⊗ₖ
            certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm2 p))) :=
  certificateWordCarrier_regroup_sum _ _ _ certificateAuxiliarySixCarrier_diagram_sum

/-- The literal original joint holomorphic coefficient action. -/
def certificateCarrierJointAction0 (t : Fin 7 × Fin 7 × Fin 7) :=
  ∑ p : Fin 120, (certificateCarrierWeight0 p : ℂ) •
    certificateTripleSourceAction certificatePhysicalFrameSystem0
      (certificateCarrierSourceAction0 p) (certificateCarrierSourceAction0 p)
      (certificateCarrierSourceAction0 p) t

/-- The literal original joint mixed coefficient action. -/
def certificateCarrierJointAction1 (t : Fin 8 × Fin 8 × Fin 8) :=
  ∑ p : Fin 12, (certificateCarrierWeight1 p : ℂ) •
    certificateTripleSourceAction certificatePhysicalFrameSystem1
      (certificateCarrierSourceAction1 p) (certificateCarrierSourceAction1 p)
      (certificateCarrierSourceAction1 p) t

/-- The literal original joint auxiliary coefficient action. -/
def certificateCarrierJointAction2 (t : Fin 7 × Fin 7 × Fin 7) :=
  ∑ p : Fin 24, (certificateCarrierWeight2 p : ℂ) •
    certificateTripleSourceAction certificatePhysicalFrameSystem2
      (certificateCarrierSourceAction2 p) (certificateCarrierSourceAction2 p)
      (certificateCarrierSourceAction2 p) t

/-- The unchanged source coefficients act on the complete physical holomorphic basis. -/
theorem certificateCarrierJointAction0_physical :
    certificateRegroupMatrix certificateQutritCarrier * certificateThreeSiteFrameSystem0.basis =
      certificateThreeSiteFrameSystem0.basis * Matrix.blockDiagonal' (fun f =>
        certificateCarrierJointAction0 (certificateThreeSiteFrameSystem0.type f)) := by
  rw [certificateQutritCarrier_regroup_sum]
  exact certificatePhysicalFrameSystem_intertwines_sum certificateThreeSiteFrameSystem0
    _ _ _ certificateCarrierSourceAction0_triple

/-- The unchanged source coefficients act on the complete physical mixed basis. -/
theorem certificateCarrierJointAction1_physical :
    certificateRegroupMatrix certificateMixedQutritCarrier * certificateThreeSiteFrameSystem1.basis =
      certificateThreeSiteFrameSystem1.basis * Matrix.blockDiagonal' (fun f =>
        certificateCarrierJointAction1 (certificateThreeSiteFrameSystem1.type f)) := by
  rw [certificateMixedQutritCarrier_regroup_sum]
  exact certificatePhysicalFrameSystem_intertwines_sum certificateThreeSiteFrameSystem1
    _ _ _ certificateCarrierSourceAction1_triple

/-- The unchanged source coefficients act on the complete physical auxiliary basis. -/
theorem certificateCarrierJointAction2_physical :
    certificateRegroupMatrix certificateAuxiliaryQutritCarrier * certificateThreeSiteFrameSystem2.basis =
      certificateThreeSiteFrameSystem2.basis * Matrix.blockDiagonal' (fun f =>
        certificateCarrierJointAction2 (certificateThreeSiteFrameSystem2.type f)) := by
  rw [certificateAuxiliaryQutritCarrier_regroup_sum]
  exact certificatePhysicalFrameSystem_intertwines_sum certificateThreeSiteFrameSystem2
    _ _ _ certificateCarrierSourceAction2_triple

end ThreeCopyQutritWerner
