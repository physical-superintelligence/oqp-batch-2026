module

public import ThreeCopyQutritWerner.CertificateX2HKeysKind
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierWeights
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData0
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData1
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData2
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData3
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData4
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData5
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierData6

@[expose] public section


/-!
# Integer trace identities of the carrier's kind parts (kernel)

`x2hG T1 T2 T3 τ k` is six times the trace of the `(τ, k)` part of one carrier cube
`A ⊗ A ⊗ A`, in terms of the local traces `T1 t = tr A_t`, `T2 t = tr A_t²`, `T3 t = tr A_t³`
(CertificateX2HKeysTrace proves this for the bridge's kind projectors). `x2hSumG τ k =
∑_p num_p · x2hG(traces of A_p)` is then `576 · trace` of the carrier's `(τ, k)` part.
Kernel checks: the trace count of every h key, the empty kinds of the sorted type triples, and
that every standard (degree 2) key has three equal types.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

open scoped BigOperators

namespace ThreeCopyQutritWerner.X2Sites

open X2

/-- All trace tables: `x2hTrAll t j p = trace (A_p(t) ^ (j + 1))`. -/
noncomputable def x2hTrAll : Fin 7 → Fin 3 → Fin 120 → ℤ :=
  ![x2hTr0, x2hTr1, x2hTr2, x2hTr3, x2hTr4, x2hTr5, x2hTr6]

/-- Six times the trace of the `(τ, k)` part of one carrier cube, from its local traces. -/
def x2hG (T1 T2 T3 : Fin 7 → ℤ) (τ : Fin 7 × Fin 7 × Fin 7) (k : ℕ) : ℤ :=
  if τ.1 = τ.2.1 ∧ τ.2.1 = τ.2.2 then
    (if k = 0 then T1 τ.1 ^ 3 + 3 * T1 τ.1 * T2 τ.1 + 2 * T3 τ.1
      else if k = 1 then T1 τ.1 ^ 3 - 3 * T1 τ.1 * T2 τ.1 + 2 * T3 τ.1
      else 4 * T1 τ.1 ^ 3 - 4 * T3 τ.1)
  else if τ.1 = τ.2.1 then
    3 * (T1 τ.1 * T1 τ.1 * T1 τ.2.2 + (if k = 0 then 1 else -1) * T2 τ.1 * T1 τ.2.2)
  else if τ.2.1 = τ.2.2 then
    3 * (T1 τ.1 * T1 τ.2.1 * T1 τ.2.1 + (if k = 0 then 1 else -1) * T1 τ.1 * T2 τ.2.1)
  else 6 * (T1 τ.1 * T1 τ.2.1 * T1 τ.2.2)

/-- `576 ·` the trace of the carrier's `(τ, k)` part. -/
noncomputable def x2hSumG (τ : Fin 7 × Fin 7 × Fin 7) (k : ℕ) : ℤ :=
  ∑ p : Fin 120, x2hNum p * x2hG (fun t => x2hTrAll t 0 p) (fun t => x2hTrAll t 1 p)
    (fun t => x2hTrAll t 2 p) τ k

/-- Mirror of the bridge's `x2NumKinds` (same body). -/
def x2hNumKinds (τ : Fin 7 × Fin 7 × Fin 7) : ℕ :=
  if τ.1 = τ.2.1 ∧ τ.2.1 = τ.2.2 then 3 else if τ.1 = τ.2.1 ∨ τ.2.1 = τ.2.2 then 2 else 1

theorem x2hCountCheck : ∀ b : x2Key 0,
    x2hSumG (x2hTau b) (x2KeyKind 0 b) = 576 * ((x2KeyDegree 0 b * x2KeySize 0 b : ℕ) : ℤ) := by
  decide +kernel

theorem x2hDeg2Check : ∀ b : x2Key 0, x2KeyDegree 0 b = 2 →
    (x2hTau b).1 = (x2hTau b).2.1 ∧ (x2hTau b).2.1 = (x2hTau b).2.2 := by
  decide +kernel

theorem x2hEmptyCheck : ∀ τ : Fin 7 × Fin 7 × Fin 7, τ.1 ≤ τ.2.1 → τ.2.1 ≤ τ.2.2 →
    ∀ k, k < x2hNumKinds τ → (∃ b : x2Key 0, x2hTau b = τ ∧ x2KeyKind 0 b = k) ∨ x2hSumG τ k = 0 := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
