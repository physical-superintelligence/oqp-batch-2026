module

public import ThreeCopyQutritWerner.CertificateCarrierActionData1_6

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction1_6_bound (p : Fin 12) :
    certificateLocalFrame1_6.submatrix (fun r => certificateLocalPivots1_6 r ∘ ⇑(certificateCarrierPerm1 p).symm) id =
      certificateCarrierAction1_6 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction1_6_bound (p : Fin 12) :
    certificateLocalGram1_6 * certificateCarrierAction1_6 p = certificateCarrierWeightedAction1_6 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction1_6_physical (p : Fin 12) :
    certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_6 =
      certificateLocalFrame1_6 * certificateCarrierAction1_6 p := by
  have h := certificateLocalFrame1_6_ordinary_action (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p)
  rwa [certificateCarrierAction1_6_bound] at h

theorem certificateCarrierWeightedAction1_6_physical (p : Fin 12) :
    certificateLocalFrame1_6ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_6 =
      certificateCarrierWeightedAction1_6 p := by
  rw [certificateLocalFrame1_6_ordinary_compression (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p),
    certificateCarrierAction1_6_bound, certificateCarrierWeightedAction1_6_bound]

end ThreeCopyQutritWerner
