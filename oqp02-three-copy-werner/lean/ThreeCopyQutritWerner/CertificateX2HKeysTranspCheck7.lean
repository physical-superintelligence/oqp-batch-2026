module

public import ThreeCopyQutritWerner.CertificateX2HKeysTransp

@[expose] public section


/-! The transposition identities of the h images, kernel checks (keys by cost). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hKeyCheck_14 : ∀ b : x2Key 0, 89 ≤ (b : ℕ) → (b : ℕ) < 91 → keyCheck b = true := by
  decide +kernel

theorem x2hKeyCheck_15 : ∀ b : x2Key 0, 91 ≤ (b : ℕ) → (b : ℕ) < 92 → keyCheck b = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
