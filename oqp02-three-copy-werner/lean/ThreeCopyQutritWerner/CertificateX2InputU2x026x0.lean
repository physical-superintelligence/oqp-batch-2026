module

public import ThreeCopyQutritWerner.CertificateX2InputK2x026

@[expose] public section


/-! Stored upper blocks of the type triple (0, 2, 6) of sector 2, row-batches a0 in [0, 1), checked by ibBatchOK. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InK2x026
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_nest ub 256 1 5 11 0 1 (v305 v305 94810963968000)

theorem ubc_0_0 : (ibBatchOK 256 55 302 11 5 0 11 0 (ks.flatMap Prod.snd) (ub_0_0).flatten = true ∧ (ub_0_0).length = 1 ∧ ∀ l ∈ ub_0_0, l.length = 5) := by decide +kernel
theorem ubc_0_1 : (ibBatchOK 256 55 302 11 5 0 11 11 (ks.flatMap Prod.snd) (ub_0_1).flatten = true ∧ (ub_0_1).length = 1 ∧ ∀ l ∈ ub_0_1, l.length = 5) := by decide +kernel
theorem ubc_0_2 : (ibBatchOK 256 55 302 11 5 0 11 22 (ks.flatMap Prod.snd) (ub_0_2).flatten = true ∧ (ub_0_2).length = 1 ∧ ∀ l ∈ ub_0_2, l.length = 5) := by decide +kernel
theorem ubc_0_3 : (ibBatchOK 256 55 302 11 5 0 11 33 (ks.flatMap Prod.snd) (ub_0_3).flatten = true ∧ (ub_0_3).length = 1 ∧ ∀ l ∈ ub_0_3, l.length = 5) := by decide +kernel
theorem ubc_0_4 : (ibBatchOK 256 55 302 11 5 0 11 44 (ks.flatMap Prod.snd) (ub_0_4).flatten = true ∧ (ub_0_4).length = 1 ∧ ∀ l ∈ ub_0_4, l.length = 5) := by decide +kernel

end ThreeCopyQutritWerner.X2.InK2x026
