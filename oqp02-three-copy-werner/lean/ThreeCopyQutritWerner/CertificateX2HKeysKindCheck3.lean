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

theorem kindCheck_c9 : ∀ b : x2Key 0, 121 ≤ (b : ℕ) → (b : ℕ) < 122 → kindCheck b = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
