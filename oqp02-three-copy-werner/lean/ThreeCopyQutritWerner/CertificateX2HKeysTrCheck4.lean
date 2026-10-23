module

public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData4
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section


/-! The trace table of the type-4 carrier action (kernel). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hTrCheck4_0 : ∀ p : Fin 120, 0 ≤ (p : ℕ) → (p : ℕ) < 15 →
    (x2hA4 p).trace = x2hTr4 0 p ∧ (x2hA4 p * x2hA4 p).trace = x2hTr4 1 p ∧
      (x2hA4 p * x2hA4 p * x2hA4 p).trace = x2hTr4 2 p := by
  decide +kernel

theorem x2hTrCheck4_1 : ∀ p : Fin 120, 15 ≤ (p : ℕ) → (p : ℕ) < 30 →
    (x2hA4 p).trace = x2hTr4 0 p ∧ (x2hA4 p * x2hA4 p).trace = x2hTr4 1 p ∧
      (x2hA4 p * x2hA4 p * x2hA4 p).trace = x2hTr4 2 p := by
  decide +kernel

theorem x2hTrCheck4_2 : ∀ p : Fin 120, 30 ≤ (p : ℕ) → (p : ℕ) < 45 →
    (x2hA4 p).trace = x2hTr4 0 p ∧ (x2hA4 p * x2hA4 p).trace = x2hTr4 1 p ∧
      (x2hA4 p * x2hA4 p * x2hA4 p).trace = x2hTr4 2 p := by
  decide +kernel

theorem x2hTrCheck4_3 : ∀ p : Fin 120, 45 ≤ (p : ℕ) → (p : ℕ) < 60 →
    (x2hA4 p).trace = x2hTr4 0 p ∧ (x2hA4 p * x2hA4 p).trace = x2hTr4 1 p ∧
      (x2hA4 p * x2hA4 p * x2hA4 p).trace = x2hTr4 2 p := by
  decide +kernel

theorem x2hTrCheck4_4 : ∀ p : Fin 120, 60 ≤ (p : ℕ) → (p : ℕ) < 75 →
    (x2hA4 p).trace = x2hTr4 0 p ∧ (x2hA4 p * x2hA4 p).trace = x2hTr4 1 p ∧
      (x2hA4 p * x2hA4 p * x2hA4 p).trace = x2hTr4 2 p := by
  decide +kernel

theorem x2hTrCheck4_5 : ∀ p : Fin 120, 75 ≤ (p : ℕ) → (p : ℕ) < 90 →
    (x2hA4 p).trace = x2hTr4 0 p ∧ (x2hA4 p * x2hA4 p).trace = x2hTr4 1 p ∧
      (x2hA4 p * x2hA4 p * x2hA4 p).trace = x2hTr4 2 p := by
  decide +kernel

theorem x2hTrCheck4_6 : ∀ p : Fin 120, 90 ≤ (p : ℕ) → (p : ℕ) < 105 →
    (x2hA4 p).trace = x2hTr4 0 p ∧ (x2hA4 p * x2hA4 p).trace = x2hTr4 1 p ∧
      (x2hA4 p * x2hA4 p * x2hA4 p).trace = x2hTr4 2 p := by
  decide +kernel

theorem x2hTrCheck4_7 : ∀ p : Fin 120, 105 ≤ (p : ℕ) → (p : ℕ) < 120 →
    (x2hA4 p).trace = x2hTr4 0 p ∧ (x2hA4 p * x2hA4 p).trace = x2hTr4 1 p ∧
      (x2hA4 p * x2hA4 p * x2hA4 p).trace = x2hTr4 2 p := by
  decide +kernel

theorem x2hTrCheck4 (p : Fin 120) :
    (x2hA4 p).trace = x2hTr4 0 p ∧ (x2hA4 p * x2hA4 p).trace = x2hTr4 1 p ∧
      (x2hA4 p * x2hA4 p * x2hA4 p).trace = x2hTr4 2 p := by
  by_cases h0 : (p : ℕ) < 15
  · exact x2hTrCheck4_0 p (by omega) h0
  by_cases h1 : (p : ℕ) < 30
  · exact x2hTrCheck4_1 p (by omega) h1
  by_cases h2 : (p : ℕ) < 45
  · exact x2hTrCheck4_2 p (by omega) h2
  by_cases h3 : (p : ℕ) < 60
  · exact x2hTrCheck4_3 p (by omega) h3
  by_cases h4 : (p : ℕ) < 75
  · exact x2hTrCheck4_4 p (by omega) h4
  by_cases h5 : (p : ℕ) < 90
  · exact x2hTrCheck4_5 p (by omega) h5
  by_cases h6 : (p : ℕ) < 105
  · exact x2hTrCheck4_6 p (by omega) h6
  · exact x2hTrCheck4_7 p (by omega) p.isLt

end ThreeCopyQutritWerner.X2Sites
