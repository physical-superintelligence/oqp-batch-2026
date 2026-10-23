module

public import ThreeCopyQutritWerner.CertificateX2InputK1x045

@[expose] public section


/-! Stored upper blocks of the type triple (0, 4, 5) of sector 1, row-batches a0 in [0, 1), checked by ibBatchOK. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InK1x045
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_nest ub 256 1 7 7 0 1 (v146 v146 94810963968000)

theorem ubc_0_0 : (ibBatchOK 256 49 302 7 7 0 7 0 (ks.flatMap Prod.snd) (ub_0_0).flatten = true ∧ (ub_0_0).length = 1 ∧ ∀ l ∈ ub_0_0, l.length = 7) := by decide +kernel
theorem ubc_0_1 : (ibBatchOK 256 49 302 7 7 0 7 7 (ks.flatMap Prod.snd) (ub_0_1).flatten = true ∧ (ub_0_1).length = 1 ∧ ∀ l ∈ ub_0_1, l.length = 7) := by decide +kernel
theorem ubc_0_2 : (ibBatchOK 256 49 302 7 7 0 7 14 (ks.flatMap Prod.snd) (ub_0_2).flatten = true ∧ (ub_0_2).length = 1 ∧ ∀ l ∈ ub_0_2, l.length = 7) := by decide +kernel
theorem ubc_0_3 : (ibBatchOK 256 49 302 7 7 0 7 21 (ks.flatMap Prod.snd) (ub_0_3).flatten = true ∧ (ub_0_3).length = 1 ∧ ∀ l ∈ ub_0_3, l.length = 7) := by decide +kernel
theorem ubc_0_4 : (ibBatchOK 256 49 302 7 7 0 7 28 (ks.flatMap Prod.snd) (ub_0_4).flatten = true ∧ (ub_0_4).length = 1 ∧ ∀ l ∈ ub_0_4, l.length = 7) := by decide +kernel
theorem ubc_0_5 : (ibBatchOK 256 49 302 7 7 0 7 35 (ks.flatMap Prod.snd) (ub_0_5).flatten = true ∧ (ub_0_5).length = 1 ∧ ∀ l ∈ ub_0_5, l.length = 7) := by decide +kernel
theorem ubc_0_6 : (ibBatchOK 256 49 302 7 7 0 7 42 (ks.flatMap Prod.snd) (ub_0_6).flatten = true ∧ (ub_0_6).length = 1 ∧ ∀ l ∈ ub_0_6, l.length = 7) := by decide +kernel

end ThreeCopyQutritWerner.X2.InK1x045
