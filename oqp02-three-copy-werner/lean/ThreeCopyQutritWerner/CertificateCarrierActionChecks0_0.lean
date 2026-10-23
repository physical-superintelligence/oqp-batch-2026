module

public import ThreeCopyQutritWerner.CertificateCarrierActionData0_0

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction0_0_bound (p : Fin 120) :
    certificateLocalFrame0_0.submatrix (fun r => certificateLocalPivots0_0 r ∘ ⇑(certificateCarrierPerm0 p).symm) id =
      certificateCarrierAction0_0 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction0_0_bound (p : Fin 120) :
    certificateLocalGram0_0 * certificateCarrierAction0_0 p = certificateCarrierWeightedAction0_0 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction0_0_physical (p : Fin 120) :
    certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_0 =
      certificateLocalFrame0_0 * certificateCarrierAction0_0 p := by
  have h := certificateLocalFrame0_0_ordinary_action (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p)
  rwa [certificateCarrierAction0_0_bound] at h

theorem certificateCarrierWeightedAction0_0_physical (p : Fin 120) :
    certificateLocalFrame0_0ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_0 =
      certificateCarrierWeightedAction0_0 p := by
  rw [certificateLocalFrame0_0_ordinary_compression (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p),
    certificateCarrierAction0_0_bound, certificateCarrierWeightedAction0_0_bound]

end ThreeCopyQutritWerner
