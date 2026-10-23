module

public import ThreeCopyQutritWerner.CertificateCarrierActionData1_7

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction1_7_bound (p : Fin 12) :
    certificateLocalFrame1_7.submatrix (fun r => certificateLocalPivots1_7 r ∘ ⇑(certificateCarrierPerm1 p).symm) id =
      certificateCarrierAction1_7 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction1_7_bound (p : Fin 12) :
    certificateLocalGram1_7 * certificateCarrierAction1_7 p = certificateCarrierWeightedAction1_7 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction1_7_physical (p : Fin 12) :
    certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_7 =
      certificateLocalFrame1_7 * certificateCarrierAction1_7 p := by
  have h := certificateLocalFrame1_7_ordinary_action (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p)
  rwa [certificateCarrierAction1_7_bound] at h

theorem certificateCarrierWeightedAction1_7_physical (p : Fin 12) :
    certificateLocalFrame1_7ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_7 =
      certificateCarrierWeightedAction1_7 p := by
  rw [certificateLocalFrame1_7_ordinary_compression (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p),
    certificateCarrierAction1_7_bound, certificateCarrierWeightedAction1_7_bound]

end ThreeCopyQutritWerner
