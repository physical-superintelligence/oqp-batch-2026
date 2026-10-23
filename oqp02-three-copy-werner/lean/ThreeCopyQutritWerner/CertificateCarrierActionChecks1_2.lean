module

public import ThreeCopyQutritWerner.CertificateCarrierActionData1_2

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction1_2_bound (p : Fin 12) :
    certificateLocalFrame1_2.submatrix (fun r => certificateLocalPivots1_2 r ∘ ⇑(certificateCarrierPerm1 p).symm) id =
      certificateCarrierAction1_2 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction1_2_bound (p : Fin 12) :
    certificateLocalGram1_2 * certificateCarrierAction1_2 p = certificateCarrierWeightedAction1_2 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction1_2_physical (p : Fin 12) :
    certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_2 =
      certificateLocalFrame1_2 * certificateCarrierAction1_2 p := by
  have h := certificateLocalFrame1_2_ordinary_action (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p)
  rwa [certificateCarrierAction1_2_bound] at h

theorem certificateCarrierWeightedAction1_2_physical (p : Fin 12) :
    certificateLocalFrame1_2ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm1 p) * certificateLocalFrame1_2 =
      certificateCarrierWeightedAction1_2 p := by
  rw [certificateLocalFrame1_2_ordinary_compression (certificateCarrierPerm1 p) (certificateCarrierPerm1_preserves p),
    certificateCarrierAction1_2_bound, certificateCarrierWeightedAction1_2_bound]

end ThreeCopyQutritWerner
