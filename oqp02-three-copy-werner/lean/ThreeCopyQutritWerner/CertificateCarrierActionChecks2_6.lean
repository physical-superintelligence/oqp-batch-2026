module

public import ThreeCopyQutritWerner.CertificateCarrierActionData2_6

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction2_6_bound (p : Fin 24) :
    certificateLocalFrame2_6.submatrix (fun r => certificateLocalPivots2_6 r ∘ ⇑(certificateCarrierPerm2 p).symm) id =
      certificateCarrierAction2_6 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction2_6_bound (p : Fin 24) :
    certificateLocalGram2_6 * certificateCarrierAction2_6 p = certificateCarrierWeightedAction2_6 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction2_6_physical (p : Fin 24) :
    certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_6 =
      certificateLocalFrame2_6 * certificateCarrierAction2_6 p := by
  have h := certificateLocalFrame2_6_ordinary_action (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p)
  rwa [certificateCarrierAction2_6_bound] at h

theorem certificateCarrierWeightedAction2_6_physical (p : Fin 24) :
    certificateLocalFrame2_6ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm2 p) * certificateLocalFrame2_6 =
      certificateCarrierWeightedAction2_6 p := by
  rw [certificateLocalFrame2_6_ordinary_compression (certificateCarrierPerm2 p) (certificateCarrierPerm2_preserves p),
    certificateCarrierAction2_6_bound, certificateCarrierWeightedAction2_6_bound]

end ThreeCopyQutritWerner
