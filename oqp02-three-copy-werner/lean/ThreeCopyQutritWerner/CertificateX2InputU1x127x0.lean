module

public import ThreeCopyQutritWerner.CertificateX2InputK1x127

@[expose] public section


/-! Stored upper blocks of the type triple (1, 2, 7) of sector 1, row-batches a0 in [0, 2), checked by ibBatchOK. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InK1x127
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_nest ub 256 2 2 6 0 2 (v175 v175 94810963968000)

theorem ubc_0_0 : (ibBatchOK 256 24 302 6 4 0 6 0 (ks.flatMap Prod.snd) (ub_0_0).flatten = true ∧ (ub_0_0).length = 2 ∧ ∀ l ∈ ub_0_0, l.length = 2) := by decide +kernel
theorem ubc_0_1 : (ibBatchOK 256 24 302 6 4 0 6 6 (ks.flatMap Prod.snd) (ub_0_1).flatten = true ∧ (ub_0_1).length = 2 ∧ ∀ l ∈ ub_0_1, l.length = 2) := by decide +kernel
theorem ubc_1_0 : (ibBatchOK 256 24 302 6 4 0 6 12 (ks.flatMap Prod.snd) (ub_1_0).flatten = true ∧ (ub_1_0).length = 2 ∧ ∀ l ∈ ub_1_0, l.length = 2) := by decide +kernel
theorem ubc_1_1 : (ibBatchOK 256 24 302 6 4 0 6 18 (ks.flatMap Prod.snd) (ub_1_1).flatten = true ∧ (ub_1_1).length = 2 ∧ ∀ l ∈ ub_1_1, l.length = 2) := by decide +kernel

end ThreeCopyQutritWerner.X2.InK1x127
