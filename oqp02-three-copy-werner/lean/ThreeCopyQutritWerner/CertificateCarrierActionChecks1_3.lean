module

public import ThreeCopyQutritWerner.CertificateCarrierActionData1_3

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction1_3_bound (p : Fin 12) :
    certificateLocalFrame1_3.submatrix (fun r => certificateLocalPivots1_3 r ∘ ⇑(certificateCarrierPerm1 p).symm) id =
      certificateCarrierAction1_3 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction1_3_bound (p : Fin 12) :
    certificateLocalGram1_3 * certificateCarrierAction1_3 p = certificateCarrierWeightedAction1_3 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction1_3_physical (p : Fin 12) :
    certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_3 =
      certificateLocalFrame1_3 * certificateCarrierAction1_3 p := by
  have h := certificateLocalFrame1_3_ordinary_action (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p)
  rwa [certificateCarrierAction1_3_bound] at h

theorem certificateCarrierWeightedAction1_3_physical (p : Fin 12) :
    certificateLocalFrame1_3ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_3 =
      certificateCarrierWeightedAction1_3 p := by
  rw [certificateLocalFrame1_3_ordinary_compression (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p),
    certificateCarrierAction1_3_bound, certificateCarrierWeightedAction1_3_bound]

end ThreeCopyQutritWerner
