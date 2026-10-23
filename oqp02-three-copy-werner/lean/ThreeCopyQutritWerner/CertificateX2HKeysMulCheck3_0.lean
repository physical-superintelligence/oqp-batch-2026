module

public import ThreeCopyQutritWerner.CertificateX2HKeysRedData
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData3
public import Mathlib.Data.Matrix.Mul

@[expose] public section


/-! Per-site multiplicativity of the type-3 carrier action on the special left factors (kernel). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hMulCheck3_0 : ∀ s : Fin 12, ∀ q : Fin 120, 120 ≤ (s : ℕ) * 120 + q →
    (s : ℕ) * 120 + q < 780 → x2hA3 (x2hLMul s q) = x2hA3 (x2hSpecial s) * x2hA3 q := by
  decide +kernel

theorem x2hMulCheck3_1 : ∀ s : Fin 12, ∀ q : Fin 120, 780 ≤ (s : ℕ) * 120 + q →
    (s : ℕ) * 120 + q < 1440 → x2hA3 (x2hLMul s q) = x2hA3 (x2hSpecial s) * x2hA3 q := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
