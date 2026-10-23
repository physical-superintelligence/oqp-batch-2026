module

public import ThreeCopyQutritWerner.CertificateCarrierActionData2_4

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction2_4_bound (p : Fin 24) :
    certificateLocalFrame2_4.submatrix (fun r => certificateLocalPivots2_4 r ∘ ⇑(certificateCarrierPerm2 p).symm) id =
      certificateCarrierAction2_4 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction2_4_bound (p : Fin 24) :
    certificateLocalGram2_4 * certificateCarrierAction2_4 p = certificateCarrierWeightedAction2_4 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction2_4_physical (p : Fin 24) :
    certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_4 =
      certificateLocalFrame2_4 * certificateCarrierAction2_4 p := by
  have h := certificateLocalFrame2_4_ordinary_action (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p)
  rwa [certificateCarrierAction2_4_bound] at h

theorem certificateCarrierWeightedAction2_4_physical (p : Fin 24) :
    certificateLocalFrame2_4ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_4 =
      certificateCarrierWeightedAction2_4 p := by
  rw [certificateLocalFrame2_4_ordinary_compression (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p),
    certificateCarrierAction2_4_bound, certificateCarrierWeightedAction2_4_bound]

end ThreeCopyQutritWerner
