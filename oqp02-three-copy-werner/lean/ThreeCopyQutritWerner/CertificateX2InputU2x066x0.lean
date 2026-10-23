module

public import ThreeCopyQutritWerner.CertificateX2InputK2x066

@[expose] public section


/-! Stored upper blocks of the type triple (0, 6, 6) of sector 2, row-batches a0 in [0, 1), checked by ibBatchOK. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InK2x066
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_nest ub 256 1 11 11 0 1 (v317 v317 94810963968000) (v318 v318 94810963968000)

theorem ubc_0_0 : (ibBatchOK 256 121 302 11 11 0 11 0 (ks.flatMap Prod.snd) (ub_0_0).flatten = true ∧ (ub_0_0).length = 1 ∧ ∀ l ∈ ub_0_0, l.length = 11) := by decide +kernel
theorem ubc_0_1 : (ibBatchOK 256 121 302 11 11 0 11 11 (ks.flatMap Prod.snd) (ub_0_1).flatten = true ∧ (ub_0_1).length = 1 ∧ ∀ l ∈ ub_0_1, l.length = 11) := by decide +kernel
theorem ubc_0_2 : (ibBatchOK 256 121 302 11 11 0 11 22 (ks.flatMap Prod.snd) (ub_0_2).flatten = true ∧ (ub_0_2).length = 1 ∧ ∀ l ∈ ub_0_2, l.length = 11) := by decide +kernel
theorem ubc_0_3 : (ibBatchOK 256 121 302 11 11 0 11 33 (ks.flatMap Prod.snd) (ub_0_3).flatten = true ∧ (ub_0_3).length = 1 ∧ ∀ l ∈ ub_0_3, l.length = 11) := by decide +kernel
theorem ubc_0_4 : (ibBatchOK 256 121 302 11 11 0 11 44 (ks.flatMap Prod.snd) (ub_0_4).flatten = true ∧ (ub_0_4).length = 1 ∧ ∀ l ∈ ub_0_4, l.length = 11) := by decide +kernel
theorem ubc_0_5 : (ibBatchOK 256 121 302 11 11 0 11 55 (ks.flatMap Prod.snd) (ub_0_5).flatten = true ∧ (ub_0_5).length = 1 ∧ ∀ l ∈ ub_0_5, l.length = 11) := by decide +kernel
theorem ubc_0_6 : (ibBatchOK 256 121 302 11 11 0 11 66 (ks.flatMap Prod.snd) (ub_0_6).flatten = true ∧ (ub_0_6).length = 1 ∧ ∀ l ∈ ub_0_6, l.length = 11) := by decide +kernel
theorem ubc_0_7 : (ibBatchOK 256 121 302 11 11 0 11 77 (ks.flatMap Prod.snd) (ub_0_7).flatten = true ∧ (ub_0_7).length = 1 ∧ ∀ l ∈ ub_0_7, l.length = 11) := by decide +kernel
theorem ubc_0_8 : (ibBatchOK 256 121 302 11 11 0 11 88 (ks.flatMap Prod.snd) (ub_0_8).flatten = true ∧ (ub_0_8).length = 1 ∧ ∀ l ∈ ub_0_8, l.length = 11) := by decide +kernel
theorem ubc_0_9 : (ibBatchOK 256 121 302 11 11 0 11 99 (ks.flatMap Prod.snd) (ub_0_9).flatten = true ∧ (ub_0_9).length = 1 ∧ ∀ l ∈ ub_0_9, l.length = 11) := by decide +kernel
theorem ubc_0_10 : (ibBatchOK 256 121 302 11 11 0 11 110 (ks.flatMap Prod.snd) (ub_0_10).flatten = true ∧ (ub_0_10).length = 1 ∧ ∀ l ∈ ub_0_10, l.length = 11) := by decide +kernel

end ThreeCopyQutritWerner.X2.InK2x066
