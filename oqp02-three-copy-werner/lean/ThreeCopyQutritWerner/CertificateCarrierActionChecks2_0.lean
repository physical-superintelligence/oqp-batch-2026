module

public import ThreeCopyQutritWerner.CertificateCarrierActionData2_0

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction2_0_bound (p : Fin 24) :
    certificateLocalFrame2_0.submatrix (fun r => certificateLocalPivots2_0 r ∘ ⇑(certificateCarrierPerm2 p).symm) id =
      certificateCarrierAction2_0 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction2_0_bound (p : Fin 24) :
    certificateLocalGram2_0 * certificateCarrierAction2_0 p = certificateCarrierWeightedAction2_0 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction2_0_physical (p : Fin 24) :
    certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_0 =
      certificateLocalFrame2_0 * certificateCarrierAction2_0 p := by
  have h := certificateLocalFrame2_0_ordinary_action (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p)
  rwa [certificateCarrierAction2_0_bound] at h

theorem certificateCarrierWeightedAction2_0_physical (p : Fin 24) :
    certificateLocalFrame2_0ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_0 =
      certificateCarrierWeightedAction2_0 p := by
  rw [certificateLocalFrame2_0_ordinary_compression (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p),
    certificateCarrierAction2_0_bound, certificateCarrierWeightedAction2_0_bound]

end ThreeCopyQutritWerner
