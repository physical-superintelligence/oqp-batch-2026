module

public import ThreeCopyQutritWerner.CertificateCarrierActionData0_4

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction0_4_bound (p : Fin 120) :
    certificateLocalFrame0_4.submatrix (fun r => certificateLocalPivots0_4 r ∘ ⇑(certificateCarrierPerm0 p).symm) id =
      certificateCarrierAction0_4 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction0_4_bound (p : Fin 120) :
    certificateLocalGram0_4 * certificateCarrierAction0_4 p = certificateCarrierWeightedAction0_4 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction0_4_physical (p : Fin 120) :
    certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_4 =
      certificateLocalFrame0_4 * certificateCarrierAction0_4 p := by
  have h := certificateLocalFrame0_4_ordinary_action (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p)
  rwa [certificateCarrierAction0_4_bound] at h

theorem certificateCarrierWeightedAction0_4_physical (p : Fin 120) :
    certificateLocalFrame0_4ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_4 =
      certificateCarrierWeightedAction0_4 p := by
  rw [certificateLocalFrame0_4_ordinary_compression (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p),
    certificateCarrierAction0_4_bound, certificateCarrierWeightedAction0_4_bound]

end ThreeCopyQutritWerner
