module

public import ThreeCopyQutritWerner.CertificateX2InputK2x234

@[expose] public section


/-! Stored upper blocks of the type triple (2, 3, 4) of sector 2, row-batches a0 in [0, 5), checked by ibBatchOK. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InK2x234
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_nest ub 256 5 5 15 0 5 (v363 v363 94810963968000)

theorem ubc_0_0 : (ibBatchOK 256 375 302 15 25 0 15 0 (ks.flatMap Prod.snd) (ub_0_0).flatten = true ∧ (ub_0_0).length = 5 ∧ ∀ l ∈ ub_0_0, l.length = 5) := by decide +kernel
theorem ubc_0_1 : (ibBatchOK 256 375 302 15 25 0 15 15 (ks.flatMap Prod.snd) (ub_0_1).flatten = true ∧ (ub_0_1).length = 5 ∧ ∀ l ∈ ub_0_1, l.length = 5) := by decide +kernel
theorem ubc_0_2 : (ibBatchOK 256 375 302 15 25 0 15 30 (ks.flatMap Prod.snd) (ub_0_2).flatten = true ∧ (ub_0_2).length = 5 ∧ ∀ l ∈ ub_0_2, l.length = 5) := by decide +kernel
theorem ubc_0_3 : (ibBatchOK 256 375 302 15 25 0 15 45 (ks.flatMap Prod.snd) (ub_0_3).flatten = true ∧ (ub_0_3).length = 5 ∧ ∀ l ∈ ub_0_3, l.length = 5) := by decide +kernel
theorem ubc_0_4 : (ibBatchOK 256 375 302 15 25 0 15 60 (ks.flatMap Prod.snd) (ub_0_4).flatten = true ∧ (ub_0_4).length = 5 ∧ ∀ l ∈ ub_0_4, l.length = 5) := by decide +kernel
theorem ubc_1_0 : (ibBatchOK 256 375 302 15 25 0 15 75 (ks.flatMap Prod.snd) (ub_1_0).flatten = true ∧ (ub_1_0).length = 5 ∧ ∀ l ∈ ub_1_0, l.length = 5) := by decide +kernel
theorem ubc_1_1 : (ibBatchOK 256 375 302 15 25 0 15 90 (ks.flatMap Prod.snd) (ub_1_1).flatten = true ∧ (ub_1_1).length = 5 ∧ ∀ l ∈ ub_1_1, l.length = 5) := by decide +kernel
theorem ubc_1_2 : (ibBatchOK 256 375 302 15 25 0 15 105 (ks.flatMap Prod.snd) (ub_1_2).flatten = true ∧ (ub_1_2).length = 5 ∧ ∀ l ∈ ub_1_2, l.length = 5) := by decide +kernel
theorem ubc_1_3 : (ibBatchOK 256 375 302 15 25 0 15 120 (ks.flatMap Prod.snd) (ub_1_3).flatten = true ∧ (ub_1_3).length = 5 ∧ ∀ l ∈ ub_1_3, l.length = 5) := by decide +kernel
theorem ubc_1_4 : (ibBatchOK 256 375 302 15 25 0 15 135 (ks.flatMap Prod.snd) (ub_1_4).flatten = true ∧ (ub_1_4).length = 5 ∧ ∀ l ∈ ub_1_4, l.length = 5) := by decide +kernel
theorem ubc_2_0 : (ibBatchOK 256 375 302 15 25 0 15 150 (ks.flatMap Prod.snd) (ub_2_0).flatten = true ∧ (ub_2_0).length = 5 ∧ ∀ l ∈ ub_2_0, l.length = 5) := by decide +kernel
theorem ubc_2_1 : (ibBatchOK 256 375 302 15 25 0 15 165 (ks.flatMap Prod.snd) (ub_2_1).flatten = true ∧ (ub_2_1).length = 5 ∧ ∀ l ∈ ub_2_1, l.length = 5) := by decide +kernel
theorem ubc_2_2 : (ibBatchOK 256 375 302 15 25 0 15 180 (ks.flatMap Prod.snd) (ub_2_2).flatten = true ∧ (ub_2_2).length = 5 ∧ ∀ l ∈ ub_2_2, l.length = 5) := by decide +kernel
theorem ubc_2_3 : (ibBatchOK 256 375 302 15 25 0 15 195 (ks.flatMap Prod.snd) (ub_2_3).flatten = true ∧ (ub_2_3).length = 5 ∧ ∀ l ∈ ub_2_3, l.length = 5) := by decide +kernel
theorem ubc_2_4 : (ibBatchOK 256 375 302 15 25 0 15 210 (ks.flatMap Prod.snd) (ub_2_4).flatten = true ∧ (ub_2_4).length = 5 ∧ ∀ l ∈ ub_2_4, l.length = 5) := by decide +kernel
theorem ubc_3_0 : (ibBatchOK 256 375 302 15 25 0 15 225 (ks.flatMap Prod.snd) (ub_3_0).flatten = true ∧ (ub_3_0).length = 5 ∧ ∀ l ∈ ub_3_0, l.length = 5) := by decide +kernel
theorem ubc_3_1 : (ibBatchOK 256 375 302 15 25 0 15 240 (ks.flatMap Prod.snd) (ub_3_1).flatten = true ∧ (ub_3_1).length = 5 ∧ ∀ l ∈ ub_3_1, l.length = 5) := by decide +kernel
theorem ubc_3_2 : (ibBatchOK 256 375 302 15 25 0 15 255 (ks.flatMap Prod.snd) (ub_3_2).flatten = true ∧ (ub_3_2).length = 5 ∧ ∀ l ∈ ub_3_2, l.length = 5) := by decide +kernel
theorem ubc_3_3 : (ibBatchOK 256 375 302 15 25 0 15 270 (ks.flatMap Prod.snd) (ub_3_3).flatten = true ∧ (ub_3_3).length = 5 ∧ ∀ l ∈ ub_3_3, l.length = 5) := by decide +kernel
theorem ubc_3_4 : (ibBatchOK 256 375 302 15 25 0 15 285 (ks.flatMap Prod.snd) (ub_3_4).flatten = true ∧ (ub_3_4).length = 5 ∧ ∀ l ∈ ub_3_4, l.length = 5) := by decide +kernel
theorem ubc_4_0 : (ibBatchOK 256 375 302 15 25 0 15 300 (ks.flatMap Prod.snd) (ub_4_0).flatten = true ∧ (ub_4_0).length = 5 ∧ ∀ l ∈ ub_4_0, l.length = 5) := by decide +kernel
theorem ubc_4_1 : (ibBatchOK 256 375 302 15 25 0 15 315 (ks.flatMap Prod.snd) (ub_4_1).flatten = true ∧ (ub_4_1).length = 5 ∧ ∀ l ∈ ub_4_1, l.length = 5) := by decide +kernel
theorem ubc_4_2 : (ibBatchOK 256 375 302 15 25 0 15 330 (ks.flatMap Prod.snd) (ub_4_2).flatten = true ∧ (ub_4_2).length = 5 ∧ ∀ l ∈ ub_4_2, l.length = 5) := by decide +kernel
theorem ubc_4_3 : (ibBatchOK 256 375 302 15 25 0 15 345 (ks.flatMap Prod.snd) (ub_4_3).flatten = true ∧ (ub_4_3).length = 5 ∧ ∀ l ∈ ub_4_3, l.length = 5) := by decide +kernel
theorem ubc_4_4 : (ibBatchOK 256 375 302 15 25 0 15 360 (ks.flatMap Prod.snd) (ub_4_4).flatten = true ∧ (ub_4_4).length = 5 ∧ ∀ l ∈ ub_4_4, l.length = 5) := by decide +kernel

end ThreeCopyQutritWerner.X2.InK2x234
