module

public import ThreeCopyQutritWerner.CertificateX2HKeysKind

@[expose] public section


/-! Kernel checks of the per-key kind/swap facts -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem kindCheck_c3 : ∀ b : x2Key 0, 102 ≤ (b : ℕ) → (b : ℕ) < 103 → kindCheck b = true := by
  decide +kernel

theorem kindCheck_c4 : ∀ b : x2Key 0, 103 ≤ (b : ℕ) → (b : ℕ) < 105 → kindCheck b = true := by
  decide +kernel

theorem kindCheck_c5 : ∀ b : x2Key 0, 105 ≤ (b : ℕ) → (b : ℕ) < 107 → kindCheck b = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
