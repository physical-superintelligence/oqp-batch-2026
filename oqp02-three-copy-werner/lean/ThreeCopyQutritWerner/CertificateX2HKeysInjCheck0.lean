module

public import ThreeCopyQutritWerner.CertificateX2HKeysInj

@[expose] public section


/-! Kernel checks of the left-inverse certificates -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem injCheck_c0 : ∀ b : x2Key 0, 0 ≤ (b : ℕ) → (b : ℕ) < 105 → injCheck b = true := by
  decide +kernel

theorem injCheck_c1 : ∀ b : x2Key 0, 105 ≤ (b : ℕ) → (b : ℕ) < 110 → injCheck b = true := by
  decide +kernel

theorem injCheck_c2 : ∀ b : x2Key 0, 110 ≤ (b : ℕ) → (b : ℕ) < 122 → injCheck b = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
