module

public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData6
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section


/-! The trace table of the type-6 carrier action (kernel). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hTrCheck6_0 : ∀ p : Fin 120, 0 ≤ (p : ℕ) → (p : ℕ) < 30 →
    (x2hA6 p).trace = x2hTr6 0 p ∧ (x2hA6 p * x2hA6 p).trace = x2hTr6 1 p ∧
      (x2hA6 p * x2hA6 p * x2hA6 p).trace = x2hTr6 2 p := by
  decide +kernel

theorem x2hTrCheck6_1 : ∀ p : Fin 120, 30 ≤ (p : ℕ) → (p : ℕ) < 60 →
    (x2hA6 p).trace = x2hTr6 0 p ∧ (x2hA6 p * x2hA6 p).trace = x2hTr6 1 p ∧
      (x2hA6 p * x2hA6 p * x2hA6 p).trace = x2hTr6 2 p := by
  decide +kernel

theorem x2hTrCheck6_2 : ∀ p : Fin 120, 60 ≤ (p : ℕ) → (p : ℕ) < 90 →
    (x2hA6 p).trace = x2hTr6 0 p ∧ (x2hA6 p * x2hA6 p).trace = x2hTr6 1 p ∧
      (x2hA6 p * x2hA6 p * x2hA6 p).trace = x2hTr6 2 p := by
  decide +kernel

theorem x2hTrCheck6_3 : ∀ p : Fin 120, 90 ≤ (p : ℕ) → (p : ℕ) < 120 →
    (x2hA6 p).trace = x2hTr6 0 p ∧ (x2hA6 p * x2hA6 p).trace = x2hTr6 1 p ∧
      (x2hA6 p * x2hA6 p * x2hA6 p).trace = x2hTr6 2 p := by
  decide +kernel

theorem x2hTrCheck6 (p : Fin 120) :
    (x2hA6 p).trace = x2hTr6 0 p ∧ (x2hA6 p * x2hA6 p).trace = x2hTr6 1 p ∧
      (x2hA6 p * x2hA6 p * x2hA6 p).trace = x2hTr6 2 p := by
  by_cases h0 : (p : ℕ) < 30
  · exact x2hTrCheck6_0 p (by omega) h0
  by_cases h1 : (p : ℕ) < 60
  · exact x2hTrCheck6_1 p (by omega) h1
  by_cases h2 : (p : ℕ) < 90
  · exact x2hTrCheck6_2 p (by omega) h2
  · exact x2hTrCheck6_3 p (by omega) p.isLt

end ThreeCopyQutritWerner.X2Sites
