module

public import ThreeCopyQutritWerner.CertificateX2HKeysRedData
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData4
public import Mathlib.Data.Matrix.Mul

@[expose] public section


/-! Per-site multiplicativity of the type-4 carrier action on the special left factors (kernel). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hMulCheck4_38 : ∀ s : Fin 12, ∀ q : Fin 120, 1260 ≤ (s : ℕ) * 120 + q →
    (s : ℕ) * 120 + q < 1290 → x2hA4 (x2hLMul s q) = x2hA4 (x2hSpecial s) * x2hA4 q := by
  decide +kernel

theorem x2hMulCheck4_39 : ∀ s : Fin 12, ∀ q : Fin 120, 1290 ≤ (s : ℕ) * 120 + q →
    (s : ℕ) * 120 + q < 1320 → x2hA4 (x2hLMul s q) = x2hA4 (x2hSpecial s) * x2hA4 q := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
