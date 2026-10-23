module

public import ThreeCopyQutritWerner.CertificateX2InputK1x036

@[expose] public section


/-! Stored upper blocks of the type triple (0, 3, 6) of sector 1, row-batches a0 in [0, 1), checked by ibBatchOK. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InK1x036
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_nest ub 256 1 9 17 0 1 (ua142 u142 3)

theorem ubc_0_0 : (ibBatchOK 256 153 302 17 9 0 17 0 (ks.flatMap Prod.snd) (ub_0_0).flatten = true ∧ (ub_0_0).length = 1 ∧ ∀ l ∈ ub_0_0, l.length = 9) := by decide +kernel
theorem ubc_0_1 : (ibBatchOK 256 153 302 17 9 0 17 17 (ks.flatMap Prod.snd) (ub_0_1).flatten = true ∧ (ub_0_1).length = 1 ∧ ∀ l ∈ ub_0_1, l.length = 9) := by decide +kernel
theorem ubc_0_2 : (ibBatchOK 256 153 302 17 9 0 17 34 (ks.flatMap Prod.snd) (ub_0_2).flatten = true ∧ (ub_0_2).length = 1 ∧ ∀ l ∈ ub_0_2, l.length = 9) := by decide +kernel
theorem ubc_0_3 : (ibBatchOK 256 153 302 17 9 0 17 51 (ks.flatMap Prod.snd) (ub_0_3).flatten = true ∧ (ub_0_3).length = 1 ∧ ∀ l ∈ ub_0_3, l.length = 9) := by decide +kernel
theorem ubc_0_4 : (ibBatchOK 256 153 302 17 9 0 17 68 (ks.flatMap Prod.snd) (ub_0_4).flatten = true ∧ (ub_0_4).length = 1 ∧ ∀ l ∈ ub_0_4, l.length = 9) := by decide +kernel
theorem ubc_0_5 : (ibBatchOK 256 153 302 17 9 0 17 85 (ks.flatMap Prod.snd) (ub_0_5).flatten = true ∧ (ub_0_5).length = 1 ∧ ∀ l ∈ ub_0_5, l.length = 9) := by decide +kernel
theorem ubc_0_6 : (ibBatchOK 256 153 302 17 9 0 17 102 (ks.flatMap Prod.snd) (ub_0_6).flatten = true ∧ (ub_0_6).length = 1 ∧ ∀ l ∈ ub_0_6, l.length = 9) := by decide +kernel
theorem ubc_0_7 : (ibBatchOK 256 153 302 17 9 0 17 119 (ks.flatMap Prod.snd) (ub_0_7).flatten = true ∧ (ub_0_7).length = 1 ∧ ∀ l ∈ ub_0_7, l.length = 9) := by decide +kernel
theorem ubc_0_8 : (ibBatchOK 256 153 302 17 9 0 17 136 (ks.flatMap Prod.snd) (ub_0_8).flatten = true ∧ (ub_0_8).length = 1 ∧ ∀ l ∈ ub_0_8, l.length = 9) := by decide +kernel

end ThreeCopyQutritWerner.X2.InK1x036
