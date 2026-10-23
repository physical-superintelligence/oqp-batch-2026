module

public import ThreeCopyQutritWerner.CertificateCarrierActionData0_2

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction0_2_bound (p : Fin 120) :
    certificateLocalFrame0_2.submatrix (fun r => certificateLocalPivots0_2 r ∘ ⇑(certificateCarrierPerm0 p).symm) id =
      certificateCarrierAction0_2 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction0_2_bound (p : Fin 120) :
    certificateLocalGram0_2 * certificateCarrierAction0_2 p = certificateCarrierWeightedAction0_2 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction0_2_physical (p : Fin 120) :
    certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_2 =
      certificateLocalFrame0_2 * certificateCarrierAction0_2 p := by
  have h := certificateLocalFrame0_2_ordinary_action (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p)
  rwa [certificateCarrierAction0_2_bound] at h

theorem certificateCarrierWeightedAction0_2_physical (p : Fin 120) :
    certificateLocalFrame0_2ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_2 =
      certificateCarrierWeightedAction0_2 p := by
  rw [certificateLocalFrame0_2_ordinary_compression (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p),
    certificateCarrierAction0_2_bound, certificateCarrierWeightedAction0_2_bound]

end ThreeCopyQutritWerner
