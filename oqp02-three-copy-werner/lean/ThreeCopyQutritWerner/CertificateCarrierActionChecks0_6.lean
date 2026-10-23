module

public import ThreeCopyQutritWerner.CertificateCarrierActionData0_6

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction0_6_bound (p : Fin 120) :
    certificateLocalFrame0_6.submatrix (fun r => certificateLocalPivots0_6 r ∘ ⇑(certificateCarrierPerm0 p).symm) id =
      certificateCarrierAction0_6 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction0_6_bound (p : Fin 120) :
    certificateLocalGram0_6 * certificateCarrierAction0_6 p = certificateCarrierWeightedAction0_6 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction0_6_physical (p : Fin 120) :
    certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_6 =
      certificateLocalFrame0_6 * certificateCarrierAction0_6 p := by
  have h := certificateLocalFrame0_6_ordinary_action (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p)
  rwa [certificateCarrierAction0_6_bound] at h

theorem certificateCarrierWeightedAction0_6_physical (p : Fin 120) :
    certificateLocalFrame0_6ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_6 =
      certificateCarrierWeightedAction0_6 p := by
  rw [certificateLocalFrame0_6_ordinary_compression (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p),
    certificateCarrierAction0_6_bound, certificateCarrierWeightedAction0_6_bound]

end ThreeCopyQutritWerner
