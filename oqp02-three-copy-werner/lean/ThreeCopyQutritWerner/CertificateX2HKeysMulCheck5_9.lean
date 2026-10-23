module

public import ThreeCopyQutritWerner.CertificateX2HKeysRedData
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData5
public import Mathlib.Data.Matrix.Mul

@[expose] public section


/-! Per-site multiplicativity of the type-5 carrier action on the special left factors (kernel). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hMulCheck5_18 : ∀ s : Fin 12, ∀ q : Fin 120, 1200 ≤ (s : ℕ) * 120 + q →
    (s : ℕ) * 120 + q < 1260 → x2hA5 (x2hLMul s q) = x2hA5 (x2hSpecial s) * x2hA5 q := by
  decide +kernel

theorem x2hMulCheck5_19 : ∀ s : Fin 12, ∀ q : Fin 120, 1260 ≤ (s : ℕ) * 120 + q →
    (s : ℕ) * 120 + q < 1320 → x2hA5 (x2hLMul s q) = x2hA5 (x2hSpecial s) * x2hA5 q := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
