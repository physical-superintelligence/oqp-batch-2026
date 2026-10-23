module

public import ThreeCopyQutritWerner.CertificateX2InputK2x044

@[expose] public section


/-! Stored upper blocks of the type triple (0, 4, 4) of sector 2, row-batches a0 in [0, 1), checked by ibBatchOK. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InK2x044
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_nest ub 256 1 15 15 0 1 (v310 v310 94810963968000) (v311 v311 94810963968000)

theorem ubc_0_0 : (ibBatchOK 256 225 302 15 15 0 15 0 (ks.flatMap Prod.snd) (ub_0_0).flatten = true ∧ (ub_0_0).length = 1 ∧ ∀ l ∈ ub_0_0, l.length = 15) := by decide +kernel
theorem ubc_0_1 : (ibBatchOK 256 225 302 15 15 0 15 15 (ks.flatMap Prod.snd) (ub_0_1).flatten = true ∧ (ub_0_1).length = 1 ∧ ∀ l ∈ ub_0_1, l.length = 15) := by decide +kernel
theorem ubc_0_2 : (ibBatchOK 256 225 302 15 15 0 15 30 (ks.flatMap Prod.snd) (ub_0_2).flatten = true ∧ (ub_0_2).length = 1 ∧ ∀ l ∈ ub_0_2, l.length = 15) := by decide +kernel
theorem ubc_0_3 : (ibBatchOK 256 225 302 15 15 0 15 45 (ks.flatMap Prod.snd) (ub_0_3).flatten = true ∧ (ub_0_3).length = 1 ∧ ∀ l ∈ ub_0_3, l.length = 15) := by decide +kernel
theorem ubc_0_4 : (ibBatchOK 256 225 302 15 15 0 15 60 (ks.flatMap Prod.snd) (ub_0_4).flatten = true ∧ (ub_0_4).length = 1 ∧ ∀ l ∈ ub_0_4, l.length = 15) := by decide +kernel
theorem ubc_0_5 : (ibBatchOK 256 225 302 15 15 0 15 75 (ks.flatMap Prod.snd) (ub_0_5).flatten = true ∧ (ub_0_5).length = 1 ∧ ∀ l ∈ ub_0_5, l.length = 15) := by decide +kernel
theorem ubc_0_6 : (ibBatchOK 256 225 302 15 15 0 15 90 (ks.flatMap Prod.snd) (ub_0_6).flatten = true ∧ (ub_0_6).length = 1 ∧ ∀ l ∈ ub_0_6, l.length = 15) := by decide +kernel
theorem ubc_0_7 : (ibBatchOK 256 225 302 15 15 0 15 105 (ks.flatMap Prod.snd) (ub_0_7).flatten = true ∧ (ub_0_7).length = 1 ∧ ∀ l ∈ ub_0_7, l.length = 15) := by decide +kernel
theorem ubc_0_8 : (ibBatchOK 256 225 302 15 15 0 15 120 (ks.flatMap Prod.snd) (ub_0_8).flatten = true ∧ (ub_0_8).length = 1 ∧ ∀ l ∈ ub_0_8, l.length = 15) := by decide +kernel
theorem ubc_0_9 : (ibBatchOK 256 225 302 15 15 0 15 135 (ks.flatMap Prod.snd) (ub_0_9).flatten = true ∧ (ub_0_9).length = 1 ∧ ∀ l ∈ ub_0_9, l.length = 15) := by decide +kernel
theorem ubc_0_10 : (ibBatchOK 256 225 302 15 15 0 15 150 (ks.flatMap Prod.snd) (ub_0_10).flatten = true ∧ (ub_0_10).length = 1 ∧ ∀ l ∈ ub_0_10, l.length = 15) := by decide +kernel
theorem ubc_0_11 : (ibBatchOK 256 225 302 15 15 0 15 165 (ks.flatMap Prod.snd) (ub_0_11).flatten = true ∧ (ub_0_11).length = 1 ∧ ∀ l ∈ ub_0_11, l.length = 15) := by decide +kernel
theorem ubc_0_12 : (ibBatchOK 256 225 302 15 15 0 15 180 (ks.flatMap Prod.snd) (ub_0_12).flatten = true ∧ (ub_0_12).length = 1 ∧ ∀ l ∈ ub_0_12, l.length = 15) := by decide +kernel
theorem ubc_0_13 : (ibBatchOK 256 225 302 15 15 0 15 195 (ks.flatMap Prod.snd) (ub_0_13).flatten = true ∧ (ub_0_13).length = 1 ∧ ∀ l ∈ ub_0_13, l.length = 15) := by decide +kernel
theorem ubc_0_14 : (ibBatchOK 256 225 302 15 15 0 15 210 (ks.flatMap Prod.snd) (ub_0_14).flatten = true ∧ (ub_0_14).length = 1 ∧ ∀ l ∈ ub_0_14, l.length = 15) := by decide +kernel

end ThreeCopyQutritWerner.X2.InK2x044
