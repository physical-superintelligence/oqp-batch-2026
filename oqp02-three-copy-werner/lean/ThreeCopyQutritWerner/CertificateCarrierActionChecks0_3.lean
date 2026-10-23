module

public import ThreeCopyQutritWerner.CertificateCarrierActionData0_3

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction0_3_bound (p : Fin 120) :
    certificateLocalFrame0_3.submatrix (fun r => certificateLocalPivots0_3 r ∘ ⇑(certificateCarrierPerm0 p).symm) id =
      certificateCarrierAction0_3 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction0_3_bound (p : Fin 120) :
    certificateLocalGram0_3 * certificateCarrierAction0_3 p = certificateCarrierWeightedAction0_3 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction0_3_physical (p : Fin 120) :
    certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_3 =
      certificateLocalFrame0_3 * certificateCarrierAction0_3 p := by
  have h := certificateLocalFrame0_3_ordinary_action (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p)
  rwa [certificateCarrierAction0_3_bound] at h

theorem certificateCarrierWeightedAction0_3_physical (p : Fin 120) :
    certificateLocalFrame0_3ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_3 =
      certificateCarrierWeightedAction0_3 p := by
  rw [certificateLocalFrame0_3_ordinary_compression (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p),
    certificateCarrierAction0_3_bound, certificateCarrierWeightedAction0_3_bound]

end ThreeCopyQutritWerner
