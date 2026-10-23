module

public import ThreeCopyQutritWerner.CertificateX2InputK1x177

@[expose] public section


/-! Stored upper blocks of the type triple (1, 7, 7) of sector 1, row-batches a0 in [0, 2), checked by ibBatchOK. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InK1x177
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_nest ub 256 2 6 6 0 2 (v194 v194 94810963968000) (v195 v195 94810963968000)

theorem ubc_0_0 : (ibBatchOK 256 72 302 6 12 0 6 0 (ks.flatMap Prod.snd) (ub_0_0).flatten = true ∧ (ub_0_0).length = 2 ∧ ∀ l ∈ ub_0_0, l.length = 6) := by decide +kernel
theorem ubc_0_1 : (ibBatchOK 256 72 302 6 12 0 6 6 (ks.flatMap Prod.snd) (ub_0_1).flatten = true ∧ (ub_0_1).length = 2 ∧ ∀ l ∈ ub_0_1, l.length = 6) := by decide +kernel
theorem ubc_0_2 : (ibBatchOK 256 72 302 6 12 0 6 12 (ks.flatMap Prod.snd) (ub_0_2).flatten = true ∧ (ub_0_2).length = 2 ∧ ∀ l ∈ ub_0_2, l.length = 6) := by decide +kernel
theorem ubc_0_3 : (ibBatchOK 256 72 302 6 12 0 6 18 (ks.flatMap Prod.snd) (ub_0_3).flatten = true ∧ (ub_0_3).length = 2 ∧ ∀ l ∈ ub_0_3, l.length = 6) := by decide +kernel
theorem ubc_0_4 : (ibBatchOK 256 72 302 6 12 0 6 24 (ks.flatMap Prod.snd) (ub_0_4).flatten = true ∧ (ub_0_4).length = 2 ∧ ∀ l ∈ ub_0_4, l.length = 6) := by decide +kernel
theorem ubc_0_5 : (ibBatchOK 256 72 302 6 12 0 6 30 (ks.flatMap Prod.snd) (ub_0_5).flatten = true ∧ (ub_0_5).length = 2 ∧ ∀ l ∈ ub_0_5, l.length = 6) := by decide +kernel
theorem ubc_1_0 : (ibBatchOK 256 72 302 6 12 0 6 36 (ks.flatMap Prod.snd) (ub_1_0).flatten = true ∧ (ub_1_0).length = 2 ∧ ∀ l ∈ ub_1_0, l.length = 6) := by decide +kernel
theorem ubc_1_1 : (ibBatchOK 256 72 302 6 12 0 6 42 (ks.flatMap Prod.snd) (ub_1_1).flatten = true ∧ (ub_1_1).length = 2 ∧ ∀ l ∈ ub_1_1, l.length = 6) := by decide +kernel
theorem ubc_1_2 : (ibBatchOK 256 72 302 6 12 0 6 48 (ks.flatMap Prod.snd) (ub_1_2).flatten = true ∧ (ub_1_2).length = 2 ∧ ∀ l ∈ ub_1_2, l.length = 6) := by decide +kernel
theorem ubc_1_3 : (ibBatchOK 256 72 302 6 12 0 6 54 (ks.flatMap Prod.snd) (ub_1_3).flatten = true ∧ (ub_1_3).length = 2 ∧ ∀ l ∈ ub_1_3, l.length = 6) := by decide +kernel
theorem ubc_1_4 : (ibBatchOK 256 72 302 6 12 0 6 60 (ks.flatMap Prod.snd) (ub_1_4).flatten = true ∧ (ub_1_4).length = 2 ∧ ∀ l ∈ ub_1_4, l.length = 6) := by decide +kernel
theorem ubc_1_5 : (ibBatchOK 256 72 302 6 12 0 6 66 (ks.flatMap Prod.snd) (ub_1_5).flatten = true ∧ (ub_1_5).length = 2 ∧ ∀ l ∈ ub_1_5, l.length = 6) := by decide +kernel

end ThreeCopyQutritWerner.X2.InK1x177
