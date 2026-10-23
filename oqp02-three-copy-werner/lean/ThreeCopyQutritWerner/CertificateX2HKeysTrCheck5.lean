module

public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData5
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section


/-! The trace table of the type-5 carrier action (kernel). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hTrCheck5_0 : ∀ p : Fin 120, 0 ≤ (p : ℕ) → (p : ℕ) < 30 →
    (x2hA5 p).trace = x2hTr5 0 p ∧ (x2hA5 p * x2hA5 p).trace = x2hTr5 1 p ∧
      (x2hA5 p * x2hA5 p * x2hA5 p).trace = x2hTr5 2 p := by
  decide +kernel

theorem x2hTrCheck5_1 : ∀ p : Fin 120, 30 ≤ (p : ℕ) → (p : ℕ) < 60 →
    (x2hA5 p).trace = x2hTr5 0 p ∧ (x2hA5 p * x2hA5 p).trace = x2hTr5 1 p ∧
      (x2hA5 p * x2hA5 p * x2hA5 p).trace = x2hTr5 2 p := by
  decide +kernel

theorem x2hTrCheck5_2 : ∀ p : Fin 120, 60 ≤ (p : ℕ) → (p : ℕ) < 90 →
    (x2hA5 p).trace = x2hTr5 0 p ∧ (x2hA5 p * x2hA5 p).trace = x2hTr5 1 p ∧
      (x2hA5 p * x2hA5 p * x2hA5 p).trace = x2hTr5 2 p := by
  decide +kernel

theorem x2hTrCheck5_3 : ∀ p : Fin 120, 90 ≤ (p : ℕ) → (p : ℕ) < 120 →
    (x2hA5 p).trace = x2hTr5 0 p ∧ (x2hA5 p * x2hA5 p).trace = x2hTr5 1 p ∧
      (x2hA5 p * x2hA5 p * x2hA5 p).trace = x2hTr5 2 p := by
  decide +kernel

theorem x2hTrCheck5 (p : Fin 120) :
    (x2hA5 p).trace = x2hTr5 0 p ∧ (x2hA5 p * x2hA5 p).trace = x2hTr5 1 p ∧
      (x2hA5 p * x2hA5 p * x2hA5 p).trace = x2hTr5 2 p := by
  by_cases h0 : (p : ℕ) < 30
  · exact x2hTrCheck5_0 p (by omega) h0
  by_cases h1 : (p : ℕ) < 60
  · exact x2hTrCheck5_1 p (by omega) h1
  by_cases h2 : (p : ℕ) < 90
  · exact x2hTrCheck5_2 p (by omega) h2
  · exact x2hTrCheck5_3 p (by omega) p.isLt

end ThreeCopyQutritWerner.X2Sites
