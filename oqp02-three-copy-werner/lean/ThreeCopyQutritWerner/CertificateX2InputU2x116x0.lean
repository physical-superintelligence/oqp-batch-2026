module

public import ThreeCopyQutritWerner.CertificateX2InputK2x116

@[expose] public section


/-! Stored upper blocks of the type triple (1, 1, 6) of sector 2, row-batches a0 in [0, 4), checked by ibBatchOK. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InK2x116
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_nest ub 256 4 4 11 0 4 (v329 v329 94810963968000) (v330 v330 94810963968000)

theorem ubc_0_0 : (ibBatchOK 256 176 302 11 16 0 11 0 (ks.flatMap Prod.snd) (ub_0_0).flatten = true ∧ (ub_0_0).length = 4 ∧ ∀ l ∈ ub_0_0, l.length = 4) := by decide +kernel
theorem ubc_0_1 : (ibBatchOK 256 176 302 11 16 0 11 11 (ks.flatMap Prod.snd) (ub_0_1).flatten = true ∧ (ub_0_1).length = 4 ∧ ∀ l ∈ ub_0_1, l.length = 4) := by decide +kernel
theorem ubc_0_2 : (ibBatchOK 256 176 302 11 16 0 11 22 (ks.flatMap Prod.snd) (ub_0_2).flatten = true ∧ (ub_0_2).length = 4 ∧ ∀ l ∈ ub_0_2, l.length = 4) := by decide +kernel
theorem ubc_0_3 : (ibBatchOK 256 176 302 11 16 0 11 33 (ks.flatMap Prod.snd) (ub_0_3).flatten = true ∧ (ub_0_3).length = 4 ∧ ∀ l ∈ ub_0_3, l.length = 4) := by decide +kernel
theorem ubc_1_0 : (ibBatchOK 256 176 302 11 16 0 11 44 (ks.flatMap Prod.snd) (ub_1_0).flatten = true ∧ (ub_1_0).length = 4 ∧ ∀ l ∈ ub_1_0, l.length = 4) := by decide +kernel
theorem ubc_1_1 : (ibBatchOK 256 176 302 11 16 0 11 55 (ks.flatMap Prod.snd) (ub_1_1).flatten = true ∧ (ub_1_1).length = 4 ∧ ∀ l ∈ ub_1_1, l.length = 4) := by decide +kernel
theorem ubc_1_2 : (ibBatchOK 256 176 302 11 16 0 11 66 (ks.flatMap Prod.snd) (ub_1_2).flatten = true ∧ (ub_1_2).length = 4 ∧ ∀ l ∈ ub_1_2, l.length = 4) := by decide +kernel
theorem ubc_1_3 : (ibBatchOK 256 176 302 11 16 0 11 77 (ks.flatMap Prod.snd) (ub_1_3).flatten = true ∧ (ub_1_3).length = 4 ∧ ∀ l ∈ ub_1_3, l.length = 4) := by decide +kernel
theorem ubc_2_0 : (ibBatchOK 256 176 302 11 16 0 11 88 (ks.flatMap Prod.snd) (ub_2_0).flatten = true ∧ (ub_2_0).length = 4 ∧ ∀ l ∈ ub_2_0, l.length = 4) := by decide +kernel
theorem ubc_2_1 : (ibBatchOK 256 176 302 11 16 0 11 99 (ks.flatMap Prod.snd) (ub_2_1).flatten = true ∧ (ub_2_1).length = 4 ∧ ∀ l ∈ ub_2_1, l.length = 4) := by decide +kernel
theorem ubc_2_2 : (ibBatchOK 256 176 302 11 16 0 11 110 (ks.flatMap Prod.snd) (ub_2_2).flatten = true ∧ (ub_2_2).length = 4 ∧ ∀ l ∈ ub_2_2, l.length = 4) := by decide +kernel
theorem ubc_2_3 : (ibBatchOK 256 176 302 11 16 0 11 121 (ks.flatMap Prod.snd) (ub_2_3).flatten = true ∧ (ub_2_3).length = 4 ∧ ∀ l ∈ ub_2_3, l.length = 4) := by decide +kernel
theorem ubc_3_0 : (ibBatchOK 256 176 302 11 16 0 11 132 (ks.flatMap Prod.snd) (ub_3_0).flatten = true ∧ (ub_3_0).length = 4 ∧ ∀ l ∈ ub_3_0, l.length = 4) := by decide +kernel
theorem ubc_3_1 : (ibBatchOK 256 176 302 11 16 0 11 143 (ks.flatMap Prod.snd) (ub_3_1).flatten = true ∧ (ub_3_1).length = 4 ∧ ∀ l ∈ ub_3_1, l.length = 4) := by decide +kernel
theorem ubc_3_2 : (ibBatchOK 256 176 302 11 16 0 11 154 (ks.flatMap Prod.snd) (ub_3_2).flatten = true ∧ (ub_3_2).length = 4 ∧ ∀ l ∈ ub_3_2, l.length = 4) := by decide +kernel
theorem ubc_3_3 : (ibBatchOK 256 176 302 11 16 0 11 165 (ks.flatMap Prod.snd) (ub_3_3).flatten = true ∧ (ub_3_3).length = 4 ∧ ∀ l ∈ ub_3_3, l.length = 4) := by decide +kernel

end ThreeCopyQutritWerner.X2.InK2x116
