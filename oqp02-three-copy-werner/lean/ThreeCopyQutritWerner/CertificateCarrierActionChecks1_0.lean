module

public import ThreeCopyQutritWerner.CertificateCarrierActionData1_0

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction1_0_bound (p : Fin 12) :
    certificateLocalFrame1_0.submatrix (fun r => certificateLocalPivots1_0 r ∘ ⇑(certificateCarrierPerm1 p).symm) id =
      certificateCarrierAction1_0 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction1_0_bound (p : Fin 12) :
    certificateLocalGram1_0 * certificateCarrierAction1_0 p = certificateCarrierWeightedAction1_0 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction1_0_physical (p : Fin 12) :
    certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_0 =
      certificateLocalFrame1_0 * certificateCarrierAction1_0 p := by
  have h := certificateLocalFrame1_0_ordinary_action (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p)
  rwa [certificateCarrierAction1_0_bound] at h

theorem certificateCarrierWeightedAction1_0_physical (p : Fin 12) :
    certificateLocalFrame1_0ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_0 =
      certificateCarrierWeightedAction1_0 p := by
  rw [certificateLocalFrame1_0_ordinary_compression (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p),
    certificateCarrierAction1_0_bound, certificateCarrierWeightedAction1_0_bound]

end ThreeCopyQutritWerner
