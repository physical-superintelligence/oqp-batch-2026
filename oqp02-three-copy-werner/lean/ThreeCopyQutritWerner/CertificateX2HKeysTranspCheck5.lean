module

public import ThreeCopyQutritWerner.CertificateX2HKeysTransp

@[expose] public section


/-! The transposition identities of the h images, kernel checks (keys by cost). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hKeyCheck_10 : ∀ b : x2Key 0, 76 ≤ (b : ℕ) → (b : ℕ) < 77 → keyCheck b = true := by
  decide +kernel

theorem x2hKeyCheck_11 : ∀ b : x2Key 0, 77 ≤ (b : ℕ) → (b : ℕ) < 78 → keyCheck b = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
