module

public import ThreeCopyQutritWerner.CertificateX2InputU2x006x0

@[expose] public section


/-! S-pipeline T-tables of the type triple (0, 0, 6) of sector 2 and their specification (sigma * x2EmbedS at every label triple). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x006
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBT ub 1 1
x2_tt_gen TT UBT 1 1 11 0

theorem shape : ∀ a0 < x2Mult 2 0, ∀ a1 < x2Mult 2 0, ((UBT.getD a0 []).getD a1 []).length = x2Mult 2 0 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult 2 0 := by
  show ∀ a0 < 1, ∀ a1 < 1, ((UBT.getD a0 []).getD a1 []).length = 1 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = 1
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact ⟨(ubc_0_0).2.1, (ubc_0_0).2.2⟩
theorem hchk : ∀ a0 < x2Mult 2 0, ∀ a1 < x2Mult 2 0, ibBatchOK 256 (x2Mult 2 0 * x2Mult 2 0 * x2Mult 2 6) 302 (x2Mult 2 6) (x2Mult 2 0 * x2Mult 2 0) 0 (x2Mult 2 6) ((a0 * x2Mult 2 0 + a1) * x2Mult 2 6) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 1, ∀ a1 < 1, ibBatchOK 256 11 302 11 1 0 11 ((a0 * 1 + a1) * 11) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact (ubc_0_0).1
theorem TTr_0 : (List.range 1).all (fun k => tRowOK UBT (nS 2 6) (pairsU (x2Mult 2 0)) ((pairsU (x2Mult 2 0)).getD (0 + k) (0, 0)) (TT.getD (0 + k) [])) = true := by decide +kernel
theorem TTrows : ∀ i < nS 2 0, tRowOK UBT (nS 2 6) (pairsU (x2Mult 2 0)) ((pairsU (x2Mult 2 0)).getD i (0, 0)) (TT.getD i []) = true := by
  show ∀ i < 1, tRowOK UBT (nS 2 6) (pairsU (x2Mult 2 0)) ((pairsU (x2Mult 2 0)).getD i (0, 0)) (TT.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOK UBT (nS 2 6) (pairsU (x2Mult 2 0)) ((pairsU (x2Mult 2 0)).getD i (0, 0)) (TT.getD i [])) 0 1 TTr_0 i (Nat.zero_le i) (by omega)

theorem spec (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN3 : N k3 = x2TrialForm 2 k3) :
    TTspecS 2 N 0 0 6 TT ∧ TCspecS 2 N 0 0 6 TT := by
  have hk := keys N hN3
  have htt := tripleSpecS 2 (by decide) N hN 0 0 6 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TT.getD i1 []).getD i0 0) (tTT_of_rows 2 (by decide) UBT 0 0 6 TT TTrows)
  exact ⟨htt, tcSpec_of_tt_eq 2 N 0 6 TT htt⟩

end ThreeCopyQutritWerner.X2.InK2x006
