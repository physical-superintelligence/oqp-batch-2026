module

public import ThreeCopyQutritWerner.CertificateCarrierActionData1_1

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction1_1_bound (p : Fin 12) :
    certificateLocalFrame1_1.submatrix (fun r => certificateLocalPivots1_1 r ∘ ⇑(certificateCarrierPerm1 p).symm) id =
      certificateCarrierAction1_1 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction1_1_bound (p : Fin 12) :
    certificateLocalGram1_1 * certificateCarrierAction1_1 p = certificateCarrierWeightedAction1_1 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction1_1_physical (p : Fin 12) :
    certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_1 =
      certificateLocalFrame1_1 * certificateCarrierAction1_1 p := by
  have h := certificateLocalFrame1_1_ordinary_action (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p)
  rwa [certificateCarrierAction1_1_bound] at h

theorem certificateCarrierWeightedAction1_1_physical (p : Fin 12) :
    certificateLocalFrame1_1ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_1 =
      certificateCarrierWeightedAction1_1 p := by
  rw [certificateLocalFrame1_1_ordinary_compression (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p),
    certificateCarrierAction1_1_bound, certificateCarrierWeightedAction1_1_bound]

end ThreeCopyQutritWerner
