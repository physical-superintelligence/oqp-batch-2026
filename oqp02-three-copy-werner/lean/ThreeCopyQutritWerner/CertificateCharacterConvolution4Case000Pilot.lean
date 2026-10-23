module

public import ThreeCopyQutritWerner.CertificateCharacter

@[expose] public section


/-! One complete original S4 character-convolution case.
The original normalization and all24 summands are retained; ordinary kernel
computation only. This pilot supplies no conclusion for other output cases. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped BigOperators
namespace ThreeCopyQutritWerner

theorem certificateCharacter_convolution4_case000_pilot :
    (∑ σ : Equiv.Perm (Fin 4),
      certificateCharacter σ * certificateCharacter (σ⁻¹ * certificatePerm4 0)) =
        12 * certificateCharacter (certificatePerm4 0) := by
  rw [certificate_sum_perm4]
  decide +kernel

end ThreeCopyQutritWerner
