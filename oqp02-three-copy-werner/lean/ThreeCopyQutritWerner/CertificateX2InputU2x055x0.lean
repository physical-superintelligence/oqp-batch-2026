module

public import ThreeCopyQutritWerner.CertificateX2InputK2x055

@[expose] public section


/-! Stored upper blocks of the type triple (0, 5, 5) of sector 2, row-batches a0 in [0, 1), checked by ibBatchOK. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InK2x055
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_nest ub 256 1 10 10 0 1 (v314 v314 94810963968000) (v315 v315 94810963968000)

theorem ubc_0_0 : (ibBatchOK 256 100 302 10 10 0 10 0 (ks.flatMap Prod.snd) (ub_0_0).flatten = true ∧ (ub_0_0).length = 1 ∧ ∀ l ∈ ub_0_0, l.length = 10) := by decide +kernel
theorem ubc_0_1 : (ibBatchOK 256 100 302 10 10 0 10 10 (ks.flatMap Prod.snd) (ub_0_1).flatten = true ∧ (ub_0_1).length = 1 ∧ ∀ l ∈ ub_0_1, l.length = 10) := by decide +kernel
theorem ubc_0_2 : (ibBatchOK 256 100 302 10 10 0 10 20 (ks.flatMap Prod.snd) (ub_0_2).flatten = true ∧ (ub_0_2).length = 1 ∧ ∀ l ∈ ub_0_2, l.length = 10) := by decide +kernel
theorem ubc_0_3 : (ibBatchOK 256 100 302 10 10 0 10 30 (ks.flatMap Prod.snd) (ub_0_3).flatten = true ∧ (ub_0_3).length = 1 ∧ ∀ l ∈ ub_0_3, l.length = 10) := by decide +kernel
theorem ubc_0_4 : (ibBatchOK 256 100 302 10 10 0 10 40 (ks.flatMap Prod.snd) (ub_0_4).flatten = true ∧ (ub_0_4).length = 1 ∧ ∀ l ∈ ub_0_4, l.length = 10) := by decide +kernel
theorem ubc_0_5 : (ibBatchOK 256 100 302 10 10 0 10 50 (ks.flatMap Prod.snd) (ub_0_5).flatten = true ∧ (ub_0_5).length = 1 ∧ ∀ l ∈ ub_0_5, l.length = 10) := by decide +kernel
theorem ubc_0_6 : (ibBatchOK 256 100 302 10 10 0 10 60 (ks.flatMap Prod.snd) (ub_0_6).flatten = true ∧ (ub_0_6).length = 1 ∧ ∀ l ∈ ub_0_6, l.length = 10) := by decide +kernel
theorem ubc_0_7 : (ibBatchOK 256 100 302 10 10 0 10 70 (ks.flatMap Prod.snd) (ub_0_7).flatten = true ∧ (ub_0_7).length = 1 ∧ ∀ l ∈ ub_0_7, l.length = 10) := by decide +kernel
theorem ubc_0_8 : (ibBatchOK 256 100 302 10 10 0 10 80 (ks.flatMap Prod.snd) (ub_0_8).flatten = true ∧ (ub_0_8).length = 1 ∧ ∀ l ∈ ub_0_8, l.length = 10) := by decide +kernel
theorem ubc_0_9 : (ibBatchOK 256 100 302 10 10 0 10 90 (ks.flatMap Prod.snd) (ub_0_9).flatten = true ∧ (ub_0_9).length = 1 ∧ ∀ l ∈ ub_0_9, l.length = 10) := by decide +kernel

end ThreeCopyQutritWerner.X2.InK2x055
