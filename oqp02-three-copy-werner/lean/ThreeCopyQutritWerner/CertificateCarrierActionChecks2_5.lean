module

public import ThreeCopyQutritWerner.CertificateCarrierActionData2_5

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction2_5_bound (p : Fin 24) :
    certificateLocalFrame2_5.submatrix (fun r => certificateLocalPivots2_5 r ∘ ⇑(certificateCarrierPerm2 p).symm) id =
      certificateCarrierAction2_5 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction2_5_bound (p : Fin 24) :
    certificateLocalGram2_5 * certificateCarrierAction2_5 p = certificateCarrierWeightedAction2_5 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction2_5_physical (p : Fin 24) :
    certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_5 =
      certificateLocalFrame2_5 * certificateCarrierAction2_5 p := by
  have h := certificateLocalFrame2_5_ordinary_action (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p)
  rwa [certificateCarrierAction2_5_bound] at h

theorem certificateCarrierWeightedAction2_5_physical (p : Fin 24) :
    certificateLocalFrame2_5ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_5 =
      certificateCarrierWeightedAction2_5 p := by
  rw [certificateLocalFrame2_5_ordinary_compression (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p),
    certificateCarrierAction2_5_bound, certificateCarrierWeightedAction2_5_bound]

end ThreeCopyQutritWerner
