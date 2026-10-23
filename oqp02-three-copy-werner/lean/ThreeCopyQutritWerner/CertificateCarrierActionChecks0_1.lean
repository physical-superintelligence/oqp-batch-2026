module

public import ThreeCopyQutritWerner.CertificateCarrierActionData0_1

@[expose] public section


/-! Exact original action binding for one source frame. Ordinary kernel arithmetic only. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000


noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner


theorem certificateCarrierAction0_1_bound (p : Fin 120) :
    certificateLocalFrame0_1.submatrix (fun r => certificateLocalPivots0_1 r ∘ ⇑(certificateCarrierPerm0 p).symm) id =
      certificateCarrierAction0_1 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierWeightedAction0_1_bound (p : Fin 120) :
    certificateLocalGram0_1 * certificateCarrierAction0_1 p = certificateCarrierWeightedAction0_1 p := by
  fin_cases p <;> decide +kernel

theorem certificateCarrierAction0_1_physical (p : Fin 120) :
    certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_1 =
      certificateLocalFrame0_1 * certificateCarrierAction0_1 p := by
  have h := certificateLocalFrame0_1_ordinary_action (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p)
  rwa [certificateCarrierAction0_1_bound] at h

theorem certificateCarrierWeightedAction0_1_physical (p : Fin 120) :
    certificateLocalFrame0_1ᵀ * certificateLocalDiagram ∅ (certificateCarrierPerm0 p) * certificateLocalFrame0_1 =
      certificateCarrierWeightedAction0_1 p := by
  rw [certificateLocalFrame0_1_ordinary_compression (certificateCarrierPerm0 p) (certificateCarrierPerm0_preserves p),
    certificateCarrierAction0_1_bound, certificateCarrierWeightedAction0_1_bound]

end ThreeCopyQutritWerner
