module

public import ThreeCopyQutritWerner.CertificateCharacter

@[expose] public section


/-! One complete original S4 character-convolution output case.
Every one of the original24 summands and the normalization12 is retained.
Closed ordinary kernel arithmetic; no precomputed convolution premise. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open scoped BigOperators
namespace ThreeCopyQutritWerner

theorem certificateCharacter_convolution4_case015 :
    (∑ σ : Equiv.Perm (Fin 4),
      certificateCharacter σ * certificateCharacter (σ⁻¹ * certificatePerm4 15)) =
        12 * certificateCharacter (certificatePerm4 15) := by
  rw [certificate_sum_perm4]
  decide +kernel

end ThreeCopyQutritWerner
