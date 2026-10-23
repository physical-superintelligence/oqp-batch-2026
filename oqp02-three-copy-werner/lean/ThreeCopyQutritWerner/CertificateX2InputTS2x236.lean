module

public import ThreeCopyQutritWerner.CertificateX2InputU2x236x0

@[expose] public section


/-! S-pipeline T-tables of the type triple (2, 3, 6) of sector 2 and their specification (sigma * x2EmbedS at every label triple). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x236
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBT ub 5 5
x2_tt_gen TT UBT 5 5 11 0
x2_tt_gen TC UBT 5 5 11 1

theorem shape : ∀ a0 < x2Mult 2 2, ∀ a1 < x2Mult 2 3, ((UBT.getD a0 []).getD a1 []).length = x2Mult 2 2 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult 2 3 := by
  show ∀ a0 < 5, ∀ a1 < 5, ((UBT.getD a0 []).getD a1 []).length = 5 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = 5
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact ⟨(ubc_0_0).2.1, (ubc_0_0).2.2⟩
  · exact ⟨(ubc_0_1).2.1, (ubc_0_1).2.2⟩
  · exact ⟨(ubc_0_2).2.1, (ubc_0_2).2.2⟩
  · exact ⟨(ubc_0_3).2.1, (ubc_0_3).2.2⟩
  · exact ⟨(ubc_0_4).2.1, (ubc_0_4).2.2⟩
  · exact ⟨(ubc_1_0).2.1, (ubc_1_0).2.2⟩
  · exact ⟨(ubc_1_1).2.1, (ubc_1_1).2.2⟩
  · exact ⟨(ubc_1_2).2.1, (ubc_1_2).2.2⟩
  · exact ⟨(ubc_1_3).2.1, (ubc_1_3).2.2⟩
  · exact ⟨(ubc_1_4).2.1, (ubc_1_4).2.2⟩
  · exact ⟨(ubc_2_0).2.1, (ubc_2_0).2.2⟩
  · exact ⟨(ubc_2_1).2.1, (ubc_2_1).2.2⟩
  · exact ⟨(ubc_2_2).2.1, (ubc_2_2).2.2⟩
  · exact ⟨(ubc_2_3).2.1, (ubc_2_3).2.2⟩
  · exact ⟨(ubc_2_4).2.1, (ubc_2_4).2.2⟩
  · exact ⟨(ubc_3_0).2.1, (ubc_3_0).2.2⟩
  · exact ⟨(ubc_3_1).2.1, (ubc_3_1).2.2⟩
  · exact ⟨(ubc_3_2).2.1, (ubc_3_2).2.2⟩
  · exact ⟨(ubc_3_3).2.1, (ubc_3_3).2.2⟩
  · exact ⟨(ubc_3_4).2.1, (ubc_3_4).2.2⟩
  · exact ⟨(ubc_4_0).2.1, (ubc_4_0).2.2⟩
  · exact ⟨(ubc_4_1).2.1, (ubc_4_1).2.2⟩
  · exact ⟨(ubc_4_2).2.1, (ubc_4_2).2.2⟩
  · exact ⟨(ubc_4_3).2.1, (ubc_4_3).2.2⟩
  · exact ⟨(ubc_4_4).2.1, (ubc_4_4).2.2⟩
theorem hchk : ∀ a0 < x2Mult 2 2, ∀ a1 < x2Mult 2 3, ibBatchOK 256 (x2Mult 2 2 * x2Mult 2 3 * x2Mult 2 6) 302 (x2Mult 2 6) (x2Mult 2 2 * x2Mult 2 3) 0 (x2Mult 2 6) ((a0 * x2Mult 2 3 + a1) * x2Mult 2 6) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 5, ∀ a1 < 5, ibBatchOK 256 275 302 11 25 0 11 ((a0 * 5 + a1) * 11) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact (ubc_0_0).1
  · exact (ubc_0_1).1
  · exact (ubc_0_2).1
  · exact (ubc_0_3).1
  · exact (ubc_0_4).1
  · exact (ubc_1_0).1
  · exact (ubc_1_1).1
  · exact (ubc_1_2).1
  · exact (ubc_1_3).1
  · exact (ubc_1_4).1
  · exact (ubc_2_0).1
  · exact (ubc_2_1).1
  · exact (ubc_2_2).1
  · exact (ubc_2_3).1
  · exact (ubc_2_4).1
  · exact (ubc_3_0).1
  · exact (ubc_3_1).1
  · exact (ubc_3_2).1
  · exact (ubc_3_3).1
  · exact (ubc_3_4).1
  · exact (ubc_4_0).1
  · exact (ubc_4_1).1
  · exact (ubc_4_2).1
  · exact (ubc_4_3).1
  · exact (ubc_4_4).1
theorem TTr_0 : (List.range 15).all (fun k => tRowOK UBT (nS 2 6) (pairsU (x2Mult 2 2)) ((pairsU (x2Mult 2 3)).getD (0 + k) (0, 0)) (TT.getD (0 + k) [])) = true := by decide +kernel
theorem TTrows : ∀ i < nS 2 3, tRowOK UBT (nS 2 6) (pairsU (x2Mult 2 2)) ((pairsU (x2Mult 2 3)).getD i (0, 0)) (TT.getD i []) = true := by
  show ∀ i < 15, tRowOK UBT (nS 2 6) (pairsU (x2Mult 2 2)) ((pairsU (x2Mult 2 3)).getD i (0, 0)) (TT.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOK UBT (nS 2 6) (pairsU (x2Mult 2 2)) ((pairsU (x2Mult 2 3)).getD i (0, 0)) (TT.getD i [])) 0 15 TTr_0 i (Nat.zero_le i) (by omega)
theorem TCr_0 : (List.range 15).all (fun k => tRowOK' UBT (nS 2 6) (pairsU (x2Mult 2 3)) ((pairsU (x2Mult 2 2)).getD (0 + k) (0, 0)) (TC.getD (0 + k) [])) = true := by decide +kernel
theorem TCrows : ∀ i < nS 2 2, tRowOK' UBT (nS 2 6) (pairsU (x2Mult 2 3)) ((pairsU (x2Mult 2 2)).getD i (0, 0)) (TC.getD i []) = true := by
  show ∀ i < 15, tRowOK' UBT (nS 2 6) (pairsU (x2Mult 2 3)) ((pairsU (x2Mult 2 2)).getD i (0, 0)) (TC.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOK' UBT (nS 2 6) (pairsU (x2Mult 2 3)) ((pairsU (x2Mult 2 2)).getD i (0, 0)) (TC.getD i [])) 0 15 TCr_0 i (Nat.zero_le i) (by omega)

theorem spec (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN74 : N k74 = x2TrialForm 2 k74) :
    TTspecS 2 N 2 3 6 TT ∧ TCspecS 2 N 2 3 6 TC := by
  have hk := keys N hN74
  have htt := tripleSpecS 2 (by decide) N hN 2 3 6 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TT.getD i1 []).getD i0 0) (tTT_of_rows 2 (by decide) UBT 2 3 6 TT TTrows)
  have htc := tripleSpecS 2 (by decide) N hN 2 3 6 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TC.getD i0 []).getD i1 0) (tTC_of_rows 2 (by decide) UBT 2 3 6 TC TCrows)
  exact ⟨htt, htc⟩

end ThreeCopyQutritWerner.X2.InK2x236
