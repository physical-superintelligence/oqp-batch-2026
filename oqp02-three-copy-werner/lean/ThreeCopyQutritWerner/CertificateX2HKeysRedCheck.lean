module

public import ThreeCopyQutritWerner.CertificateX2HKeysRedData
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierWeights
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section


/-! Kernel checks of the reduction data (bijective left multiplications, the Q recurrence,
Q_6 = 672 chi, num = (1 - (1 2) - (3 4) + (1 2)(3 4)) chi, (1 2)(3 4) = (1 2)·(3 4)). -/

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

theorem x2hMulDiv : ∀ s : Fin 12, ∀ r : Fin 120, x2hLMul s (x2hLDiv s r) = r := by decide +kernel

theorem x2hDivMul : ∀ s : Fin 12, ∀ q : Fin 120, x2hLDiv s (x2hLMul s q) = q := by decide +kernel

theorem x2hLMul0 : ∀ q : Fin 120, x2hLMul 0 q = q := by decide +kernel

theorem x2hQ0 : ∀ r : Fin 120, x2hQ 0 r = if r = x2hSpecial 0 then 1 else 0 := by decide +kernel

theorem x2hQstep : ∀ i : Fin 6, ∀ r : Fin 120,
    x2hQ i.succ r = (∑ u : Fin 10, x2hQ i.castSucc (x2hLDiv u.succ.castSucc r)) - x2hCt i * x2hQ i.castSucc r := by
  decide +kernel

theorem x2hQ6 : ∀ r : Fin 120, x2hQ 6 r = 672 * x2hChi r := by decide +kernel

theorem x2hDstep : ∀ i : Fin 6, x2hD i.succ = x2hD i.castSucc * (2 - x2hCt i) := by decide +kernel

theorem x2hD0 : x2hD 0 = 1 := by decide +kernel

theorem x2hD6 : x2hD 6 = 16128 := by decide +kernel

theorem x2hNumChi : ∀ r : Fin 120,
    x2hNum r = x2hChi r - x2hChi (x2hLDiv 5 r) - x2hChi (x2hLDiv 10 r) + x2hChi (x2hLDiv 11 r) := by
  decide +kernel

theorem x2hSpecial11 : x2hLMul 5 (x2hSpecial 10) = x2hSpecial 11 := by decide +kernel

end ThreeCopyQutritWerner.X2Sites
