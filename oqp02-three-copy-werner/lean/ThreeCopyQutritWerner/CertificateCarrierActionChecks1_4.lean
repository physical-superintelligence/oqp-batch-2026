module

public import ThreeCopyQutritWerner.CertificateCarrierActionData1_4

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction1_4_bound (p : Fin 12) :
    certificateLocalFrame1_4.submatrix (fun r => certificateLocalPivots1_4 r ∘ ⇑(certificateCarrierPerm1 p).symm) id =
      certificateCarrierAction1_4 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction1_4_bound (p : Fin 12) :
    certificateLocalGram1_4 * certificateCarrierAction1_4 p = certificateCarrierWeightedAction1_4 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction1_4_physical (p : Fin 12) :
    certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_4 =
      certificateLocalFrame1_4 * certificateCarrierAction1_4 p := by
  have h := certificateLocalFrame1_4_ordinary_action (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p)
  rwa [certificateCarrierAction1_4_bound] at h

theorem certificateCarrierWeightedAction1_4_physical (p : Fin 12) :
    certificateLocalFrame1_4ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_4 =
      certificateCarrierWeightedAction1_4 p := by
  rw [certificateLocalFrame1_4_ordinary_compression (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p),
    certificateCarrierAction1_4_bound, certificateCarrierWeightedAction1_4_bound]

end ThreeCopyQutritWerner
