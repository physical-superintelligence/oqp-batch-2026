module

public import ThreeCopyQutritWerner.CertificateX2InputU2x055x0

@[expose] public section


/-! S-pipeline T-tables of the type triple (0, 5, 5) of sector 2 and their specification (sigma * x2EmbedS at every label triple). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x055
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBT ub 1 10
x2_tt_gen TT UBT 1 10 10 0
x2_tt_gen TC UBT 1 10 10 1

theorem shape : ∀ a0 < x2Mult 2 0, ∀ a1 < x2Mult 2 5, ((UBT.getD a0 []).getD a1 []).length = x2Mult 2 0 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult 2 5 := by
  show ∀ a0 < 1, ∀ a1 < 10, ((UBT.getD a0 []).getD a1 []).length = 1 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = 10
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact ⟨(ubc_0_0).2.1, (ubc_0_0).2.2⟩
  · exact ⟨(ubc_0_1).2.1, (ubc_0_1).2.2⟩
  · exact ⟨(ubc_0_2).2.1, (ubc_0_2).2.2⟩
  · exact ⟨(ubc_0_3).2.1, (ubc_0_3).2.2⟩
  · exact ⟨(ubc_0_4).2.1, (ubc_0_4).2.2⟩
  · exact ⟨(ubc_0_5).2.1, (ubc_0_5).2.2⟩
  · exact ⟨(ubc_0_6).2.1, (ubc_0_6).2.2⟩
  · exact ⟨(ubc_0_7).2.1, (ubc_0_7).2.2⟩
  · exact ⟨(ubc_0_8).2.1, (ubc_0_8).2.2⟩
  · exact ⟨(ubc_0_9).2.1, (ubc_0_9).2.2⟩
theorem hchk : ∀ a0 < x2Mult 2 0, ∀ a1 < x2Mult 2 5, ibBatchOK 256 (x2Mult 2 0 * x2Mult 2 5 * x2Mult 2 5) 302 (x2Mult 2 5) (x2Mult 2 0 * x2Mult 2 5) 0 (x2Mult 2 5) ((a0 * x2Mult 2 5 + a1) * x2Mult 2 5) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 1, ∀ a1 < 10, ibBatchOK 256 100 302 10 10 0 10 ((a0 * 10 + a1) * 10) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact (ubc_0_0).1
  · exact (ubc_0_1).1
  · exact (ubc_0_2).1
  · exact (ubc_0_3).1
  · exact (ubc_0_4).1
  · exact (ubc_0_5).1
  · exact (ubc_0_6).1
  · exact (ubc_0_7).1
  · exact (ubc_0_8).1
  · exact (ubc_0_9).1
theorem TTr_0 : (List.range 55).all (fun k => tRowOK UBT (nS 2 5) (pairsU (x2Mult 2 0)) ((pairsU (x2Mult 2 5)).getD (0 + k) (0, 0)) (TT.getD (0 + k) [])) = true := by decide +kernel
theorem TTrows : ∀ i < nS 2 5, tRowOK UBT (nS 2 5) (pairsU (x2Mult 2 0)) ((pairsU (x2Mult 2 5)).getD i (0, 0)) (TT.getD i []) = true := by
  show ∀ i < 55, tRowOK UBT (nS 2 5) (pairsU (x2Mult 2 0)) ((pairsU (x2Mult 2 5)).getD i (0, 0)) (TT.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOK UBT (nS 2 5) (pairsU (x2Mult 2 0)) ((pairsU (x2Mult 2 5)).getD i (0, 0)) (TT.getD i [])) 0 55 TTr_0 i (Nat.zero_le i) (by omega)
theorem TCr_0 : (List.range 1).all (fun k => tRowOK' UBT (nS 2 5) (pairsU (x2Mult 2 5)) ((pairsU (x2Mult 2 0)).getD (0 + k) (0, 0)) (TC.getD (0 + k) [])) = true := by decide +kernel
theorem TCrows : ∀ i < nS 2 0, tRowOK' UBT (nS 2 5) (pairsU (x2Mult 2 5)) ((pairsU (x2Mult 2 0)).getD i (0, 0)) (TC.getD i []) = true := by
  show ∀ i < 1, tRowOK' UBT (nS 2 5) (pairsU (x2Mult 2 5)) ((pairsU (x2Mult 2 0)).getD i (0, 0)) (TC.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOK' UBT (nS 2 5) (pairsU (x2Mult 2 5)) ((pairsU (x2Mult 2 0)).getD i (0, 0)) (TC.getD i [])) 0 1 TCr_0 i (Nat.zero_le i) (by omega)

theorem spec (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN23 : N k23 = x2TrialForm 2 k23) (hN24 : N k24 = x2TrialForm 2 k24) :
    TTspecS 2 N 0 5 5 TT ∧ TCspecS 2 N 0 5 5 TC := by
  have hk := keys N hN23 hN24
  have htt := tripleSpecS 2 (by decide) N hN 0 5 5 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TT.getD i1 []).getD i0 0) (tTT_of_rows 2 (by decide) UBT 0 5 5 TT TTrows)
  have htc := tripleSpecS 2 (by decide) N hN 0 5 5 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TC.getD i0 []).getD i1 0) (tTC_of_rows 2 (by decide) UBT 0 5 5 TC TCrows)
  exact ⟨htt, htc⟩

end ThreeCopyQutritWerner.X2.InK2x055
