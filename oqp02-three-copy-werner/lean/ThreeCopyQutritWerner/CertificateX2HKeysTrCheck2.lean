module

public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData2
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section


/-! The trace table of the type-2 carrier action (kernel). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hTrCheck2_0 : ∀ p : Fin 120, 0 ≤ (p : ℕ) → (p : ℕ) < 120 →
    (x2hA2 p).trace = x2hTr2 0 p ∧ (x2hA2 p * x2hA2 p).trace = x2hTr2 1 p ∧
      (x2hA2 p * x2hA2 p * x2hA2 p).trace = x2hTr2 2 p := by
  decide +kernel

theorem x2hTrCheck2 (p : Fin 120) :
    (x2hA2 p).trace = x2hTr2 0 p ∧ (x2hA2 p * x2hA2 p).trace = x2hTr2 1 p ∧
      (x2hA2 p * x2hA2 p * x2hA2 p).trace = x2hTr2 2 p := by
  · exact x2hTrCheck2_0 p (by omega) p.isLt

end ThreeCopyQutritWerner.X2Sites
