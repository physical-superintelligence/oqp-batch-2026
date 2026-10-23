module

public import ThreeCopyQutritWerner.CertificateCarrierActionData2_3

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction2_3_bound (p : Fin 24) :
    certificateLocalFrame2_3.submatrix (fun r => certificateLocalPivots2_3 r ∘ ⇑(certificateCarrierPerm2 p).symm) id =
      certificateCarrierAction2_3 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction2_3_bound (p : Fin 24) :
    certificateLocalGram2_3 * certificateCarrierAction2_3 p = certificateCarrierWeightedAction2_3 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction2_3_physical (p : Fin 24) :
    certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_3 =
      certificateLocalFrame2_3 * certificateCarrierAction2_3 p := by
  have h := certificateLocalFrame2_3_ordinary_action (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p)
  rwa [certificateCarrierAction2_3_bound] at h

theorem certificateCarrierWeightedAction2_3_physical (p : Fin 24) :
    certificateLocalFrame2_3ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_3 =
      certificateCarrierWeightedAction2_3 p := by
  rw [certificateLocalFrame2_3_ordinary_compression (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p),
    certificateCarrierAction2_3_bound, certificateCarrierWeightedAction2_3_bound]

end ThreeCopyQutritWerner
