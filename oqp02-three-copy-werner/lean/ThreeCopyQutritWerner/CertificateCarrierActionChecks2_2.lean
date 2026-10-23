module

public import ThreeCopyQutritWerner.CertificateCarrierActionData2_2

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction2_2_bound (p : Fin 24) :
    certificateLocalFrame2_2.submatrix (fun r => certificateLocalPivots2_2 r ∘ ⇑(certificateCarrierPerm2 p).symm) id =
      certificateCarrierAction2_2 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction2_2_bound (p : Fin 24) :
    certificateLocalGram2_2 * certificateCarrierAction2_2 p = certificateCarrierWeightedAction2_2 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction2_2_physical (p : Fin 24) :
    certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_2 =
      certificateLocalFrame2_2 * certificateCarrierAction2_2 p := by
  have h := certificateLocalFrame2_2_ordinary_action (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p)
  rwa [certificateCarrierAction2_2_bound] at h

theorem certificateCarrierWeightedAction2_2_physical (p : Fin 24) :
    certificateLocalFrame2_2ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_2 =
      certificateCarrierWeightedAction2_2 p := by
  rw [certificateLocalFrame2_2_ordinary_compression (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p),
    certificateCarrierAction2_2_bound, certificateCarrierWeightedAction2_2_bound]

end ThreeCopyQutritWerner
