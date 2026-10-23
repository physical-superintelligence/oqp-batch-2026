module

public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData0
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section


/-! The trace table of the type-0 carrier action (kernel). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hTrCheck0_0 : ∀ p : Fin 120, 0 ≤ (p : ℕ) → (p : ℕ) < 120 →
    (x2hA0 p).trace = x2hTr0 0 p ∧ (x2hA0 p * x2hA0 p).trace = x2hTr0 1 p ∧
      (x2hA0 p * x2hA0 p * x2hA0 p).trace = x2hTr0 2 p := by
  decide +kernel

theorem x2hTrCheck0 (p : Fin 120) :
    (x2hA0 p).trace = x2hTr0 0 p ∧ (x2hA0 p * x2hA0 p).trace = x2hTr0 1 p ∧
      (x2hA0 p * x2hA0 p * x2hA0 p).trace = x2hTr0 2 p := by
  · exact x2hTrCheck0_0 p (by omega) p.isLt

end ThreeCopyQutritWerner.X2Sites
