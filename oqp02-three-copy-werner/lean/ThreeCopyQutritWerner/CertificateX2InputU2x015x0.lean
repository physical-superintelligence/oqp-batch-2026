module

public import ThreeCopyQutritWerner.CertificateX2InputK2x015

@[expose] public section


/-! Stored upper blocks of the type triple (0, 1, 5) of sector 2, row-batches a0 in [0, 1), checked by ibBatchOK. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InK2x015
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_nest ub 256 1 4 10 0 1 (v299 v299 94810963968000)

theorem ubc_0_0 : (ibBatchOK 256 40 302 10 4 0 10 0 (ks.flatMap Prod.snd) (ub_0_0).flatten = true ∧ (ub_0_0).length = 1 ∧ ∀ l ∈ ub_0_0, l.length = 4) := by decide +kernel
theorem ubc_0_1 : (ibBatchOK 256 40 302 10 4 0 10 10 (ks.flatMap Prod.snd) (ub_0_1).flatten = true ∧ (ub_0_1).length = 1 ∧ ∀ l ∈ ub_0_1, l.length = 4) := by decide +kernel
theorem ubc_0_2 : (ibBatchOK 256 40 302 10 4 0 10 20 (ks.flatMap Prod.snd) (ub_0_2).flatten = true ∧ (ub_0_2).length = 1 ∧ ∀ l ∈ ub_0_2, l.length = 4) := by decide +kernel
theorem ubc_0_3 : (ibBatchOK 256 40 302 10 4 0 10 30 (ks.flatMap Prod.snd) (ub_0_3).flatten = true ∧ (ub_0_3).length = 1 ∧ ∀ l ∈ ub_0_3, l.length = 4) := by decide +kernel

end ThreeCopyQutritWerner.X2.InK2x015
