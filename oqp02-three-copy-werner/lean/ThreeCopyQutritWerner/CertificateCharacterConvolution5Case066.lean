module

public import ThreeCopyQutritWerner.CertificateCharacter

@[expose] public section


/-! One complete original S5 character-convolution output case.
Every one of the original120 summands and the normalization24 is retained.
Closed ordinary kernel arithmetic; no precomputed convolution premise. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open scoped BigOperators
namespace ThreeCopyQutritWerner

theorem certificateCharacter_convolution5_case066 :
    (∑ σ : Equiv.Perm (Fin 5),
      certificateCharacter σ * certificateCharacter (σ⁻¹ * certificatePerm5 66)) =
        24 * certificateCharacter (certificatePerm5 66) := by
  rw [certificate_sum_perm5]
  decide +kernel

end ThreeCopyQutritWerner
