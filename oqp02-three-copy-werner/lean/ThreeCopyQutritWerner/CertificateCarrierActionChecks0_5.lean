module

public import ThreeCopyQutritWerner.CertificateCarrierActionData0_5

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction0_5_bound (p : Fin 120) :
    certificateLocalFrame0_5.submatrix (fun r => certificateLocalPivots0_5 r ∘ ⇑(certificateCarrierPerm0 p).symm) id =
      certificateCarrierAction0_5 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction0_5_bound (p : Fin 120) :
    certificateLocalGram0_5 * certificateCarrierAction0_5 p = certificateCarrierWeightedAction0_5 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction0_5_physical (p : Fin 120) :
    certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_5 =
      certificateLocalFrame0_5 * certificateCarrierAction0_5 p := by
  have h := certificateLocalFrame0_5_ordinary_action (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p)
  rwa [certificateCarrierAction0_5_bound] at h

theorem certificateCarrierWeightedAction0_5_physical (p : Fin 120) :
    certificateLocalFrame0_5ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_5 =
      certificateCarrierWeightedAction0_5 p := by
  rw [certificateLocalFrame0_5_ordinary_compression (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p),
    certificateCarrierAction0_5_bound, certificateCarrierWeightedAction0_5_bound]

end ThreeCopyQutritWerner
