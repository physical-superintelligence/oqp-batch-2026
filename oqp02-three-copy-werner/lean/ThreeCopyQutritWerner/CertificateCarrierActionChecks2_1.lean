module

public import ThreeCopyQutritWerner.CertificateCarrierActionData2_1

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction2_1_bound (p : Fin 24) :
    certificateLocalFrame2_1.submatrix (fun r => certificateLocalPivots2_1 r ∘ ⇑(certificateCarrierPerm2 p).symm) id =
      certificateCarrierAction2_1 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction2_1_bound (p : Fin 24) :
    certificateLocalGram2_1 * certificateCarrierAction2_1 p = certificateCarrierWeightedAction2_1 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction2_1_physical (p : Fin 24) :
    certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_1 =
      certificateLocalFrame2_1 * certificateCarrierAction2_1 p := by
  have h := certificateLocalFrame2_1_ordinary_action (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p)
  rwa [certificateCarrierAction2_1_bound] at h

theorem certificateCarrierWeightedAction2_1_physical (p : Fin 24) :
    certificateLocalFrame2_1ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_1 =
      certificateCarrierWeightedAction2_1 p := by
  rw [certificateLocalFrame2_1_ordinary_compression (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p),
    certificateCarrierAction2_1_bound, certificateCarrierWeightedAction2_1_bound]

end ThreeCopyQutritWerner
