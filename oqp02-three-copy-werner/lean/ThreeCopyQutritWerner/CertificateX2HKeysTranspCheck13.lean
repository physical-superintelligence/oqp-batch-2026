module

public import ThreeCopyQutritWerner.CertificateX2HKeysTransp

@[expose] public section


/-! The transposition identities of the h images, kernel checks (keys by cost). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hKeyCheck_26 : ∀ b : x2Key 0, 105 ≤ (b : ℕ) → (b : ℕ) < 106 → keyCheck b = true := by
  decide +kernel

theorem x2hKeyCheck_27 : ∀ b : x2Key 0, 106 ≤ (b : ℕ) → (b : ℕ) < 107 → keyCheck b = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
