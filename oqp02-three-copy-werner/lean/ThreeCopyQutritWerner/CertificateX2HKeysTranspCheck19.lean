module

public import ThreeCopyQutritWerner.CertificateX2HKeysTransp

@[expose] public section


/-! The transposition identities of the h images, kernel checks (keys by cost). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hKeyCheck_38 : ∀ b : x2Key 0, 118 ≤ (b : ℕ) → (b : ℕ) < 119 → keyCheck b = true := by
  decide +kernel

theorem x2hKeyCheck_39 : ∀ b : x2Key 0, 119 ≤ (b : ℕ) → (b : ℕ) < 121 → keyCheck b = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
