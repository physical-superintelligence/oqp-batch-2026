module

public import ThreeCopyQutritWerner.CertificateX2InputK1x006

@[expose] public section


/-! Stored upper blocks of the type triple (0, 0, 6) of sector 1, row-batches a0 in [0, 1), checked by ibBatchOK. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InK1x006
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_nest ub 256 1 1 17 0 1 (ua125 u125 3)

theorem ubc_0_0 : (ibBatchOK 256 17 302 17 1 0 17 0 (ks.flatMap Prod.snd) (ub_0_0).flatten = true ∧ (ub_0_0).length = 1 ∧ ∀ l ∈ ub_0_0, l.length = 1) := by decide +kernel

end ThreeCopyQutritWerner.X2.InK1x006
