module

public import ThreeCopyQutritWerner.CertificateCharacter

@[expose] public section


/-! One complete original S5 character-convolution case.
The original normalization and all120 summands are retained; ordinary kernel
computation only. This pilot supplies no conclusion for other output cases. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open scoped BigOperators
namespace ThreeCopyQutritWerner

theorem certificateCharacter_convolution5_case000_pilot :
    (∑ σ : Equiv.Perm (Fin 5),
      certificateCharacter σ * certificateCharacter (σ⁻¹ * certificatePerm5 0)) =
        24 * certificateCharacter (certificatePerm5 0) := by
  rw [certificate_sum_perm5]
  decide +kernel

end ThreeCopyQutritWerner
