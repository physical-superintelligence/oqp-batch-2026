module

public import ThreeCopyQutritWerner.CertificateCarrierActionData1_5

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction1_5_bound (p : Fin 12) :
    certificateLocalFrame1_5.submatrix (fun r => certificateLocalPivots1_5 r ∘ ⇑(certificateCarrierPerm1 p).symm) id =
      certificateCarrierAction1_5 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction1_5_bound (p : Fin 12) :
    certificateLocalGram1_5 * certificateCarrierAction1_5 p = certificateCarrierWeightedAction1_5 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction1_5_physical (p : Fin 12) :
    certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_5 =
      certificateLocalFrame1_5 * certificateCarrierAction1_5 p := by
  have h := certificateLocalFrame1_5_ordinary_action (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p)
  rwa [certificateCarrierAction1_5_bound] at h

theorem certificateCarrierWeightedAction1_5_physical (p : Fin 12) :
    certificateLocalFrame1_5ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_5 =
      certificateCarrierWeightedAction1_5 p := by
  rw [certificateLocalFrame1_5_ordinary_compression (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p),
    certificateCarrierAction1_5_bound, certificateCarrierWeightedAction1_5_bound]

end ThreeCopyQutritWerner
