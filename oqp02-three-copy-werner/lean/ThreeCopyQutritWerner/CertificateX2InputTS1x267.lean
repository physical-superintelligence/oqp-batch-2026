module

public import ThreeCopyQutritWerner.CertificateX2InputU1x267x0

@[expose] public section


/-! S-pipeline T-tables of the type triple (2, 6, 7) of sector 1 and their specification (sigma * x2EmbedS at every label triple). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x267
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBT ub 2 17
x2_tt_gen TT UBT 2 17 6 0
x2_tt_gen TC UBT 2 17 6 1

theorem shape : ∀ a0 < x2Mult 1 2, ∀ a1 < x2Mult 1 6, ((UBT.getD a0 []).getD a1 []).length = x2Mult 1 2 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult 1 6 := by
  show ∀ a0 < 2, ∀ a1 < 17, ((UBT.getD a0 []).getD a1 []).length = 2 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = 17
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
  · exact ⟨(ubc_0_10).2.1, (ubc_0_10).2.2⟩
  · exact ⟨(ubc_0_11).2.1, (ubc_0_11).2.2⟩
  · exact ⟨(ubc_0_12).2.1, (ubc_0_12).2.2⟩
  · exact ⟨(ubc_0_13).2.1, (ubc_0_13).2.2⟩
  · exact ⟨(ubc_0_14).2.1, (ubc_0_14).2.2⟩
  · exact ⟨(ubc_0_15).2.1, (ubc_0_15).2.2⟩
  · exact ⟨(ubc_0_16).2.1, (ubc_0_16).2.2⟩
  · exact ⟨(ubc_1_0).2.1, (ubc_1_0).2.2⟩
  · exact ⟨(ubc_1_1).2.1, (ubc_1_1).2.2⟩
  · exact ⟨(ubc_1_2).2.1, (ubc_1_2).2.2⟩
  · exact ⟨(ubc_1_3).2.1, (ubc_1_3).2.2⟩
  · exact ⟨(ubc_1_4).2.1, (ubc_1_4).2.2⟩
  · exact ⟨(ubc_1_5).2.1, (ubc_1_5).2.2⟩
  · exact ⟨(ubc_1_6).2.1, (ubc_1_6).2.2⟩
  · exact ⟨(ubc_1_7).2.1, (ubc_1_7).2.2⟩
  · exact ⟨(ubc_1_8).2.1, (ubc_1_8).2.2⟩
  · exact ⟨(ubc_1_9).2.1, (ubc_1_9).2.2⟩
  · exact ⟨(ubc_1_10).2.1, (ubc_1_10).2.2⟩
  · exact ⟨(ubc_1_11).2.1, (ubc_1_11).2.2⟩
  · exact ⟨(ubc_1_12).2.1, (ubc_1_12).2.2⟩
  · exact ⟨(ubc_1_13).2.1, (ubc_1_13).2.2⟩
  · exact ⟨(ubc_1_14).2.1, (ubc_1_14).2.2⟩
  · exact ⟨(ubc_1_15).2.1, (ubc_1_15).2.2⟩
  · exact ⟨(ubc_1_16).2.1, (ubc_1_16).2.2⟩
theorem hchk : ∀ a0 < x2Mult 1 2, ∀ a1 < x2Mult 1 6, ibBatchOK 256 (x2Mult 1 2 * x2Mult 1 6 * x2Mult 1 7) 302 (x2Mult 1 7) (x2Mult 1 2 * x2Mult 1 6) 0 (x2Mult 1 7) ((a0 * x2Mult 1 6 + a1) * x2Mult 1 7) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 2, ∀ a1 < 17, ibBatchOK 256 204 302 6 34 0 6 ((a0 * 17 + a1) * 6) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true
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
  · exact (ubc_0_10).1
  · exact (ubc_0_11).1
  · exact (ubc_0_12).1
  · exact (ubc_0_13).1
  · exact (ubc_0_14).1
  · exact (ubc_0_15).1
  · exact (ubc_0_16).1
  · exact (ubc_1_0).1
  · exact (ubc_1_1).1
  · exact (ubc_1_2).1
  · exact (ubc_1_3).1
  · exact (ubc_1_4).1
  · exact (ubc_1_5).1
  · exact (ubc_1_6).1
  · exact (ubc_1_7).1
  · exact (ubc_1_8).1
  · exact (ubc_1_9).1
  · exact (ubc_1_10).1
  · exact (ubc_1_11).1
  · exact (ubc_1_12).1
  · exact (ubc_1_13).1
  · exact (ubc_1_14).1
  · exact (ubc_1_15).1
  · exact (ubc_1_16).1
theorem TTr_0 : (List.range 153).all (fun k => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 2)) ((pairsU (x2Mult 1 6)).getD (0 + k) (0, 0)) (TT.getD (0 + k) [])) = true := by decide +kernel
theorem TTrows : ∀ i < nS 1 6, tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 2)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i []) = true := by
  show ∀ i < 153, tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 2)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 2)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i [])) 0 153 TTr_0 i (Nat.zero_le i) (by omega)
theorem TCr_0 : (List.range 3).all (fun k => tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 2)).getD (0 + k) (0, 0)) (TC.getD (0 + k) [])) = true := by decide +kernel
theorem TCrows : ∀ i < nS 1 2, tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 2)).getD i (0, 0)) (TC.getD i []) = true := by
  show ∀ i < 3, tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 2)).getD i (0, 0)) (TC.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 2)).getD i (0, 0)) (TC.getD i [])) 0 3 TCr_0 i (Nat.zero_le i) (by omega)

theorem spec (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN101 : N k101 = x2TrialForm 1 k101) :
    TTspecS 1 N 2 6 7 TT ∧ TCspecS 1 N 2 6 7 TC := by
  have hk := keys N hN101
  have htt := tripleSpecS 1 (by decide) N hN 2 6 7 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TT.getD i1 []).getD i0 0) (tTT_of_rows 1 (by decide) UBT 2 6 7 TT TTrows)
  have htc := tripleSpecS 1 (by decide) N hN 2 6 7 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TC.getD i0 []).getD i1 0) (tTC_of_rows 1 (by decide) UBT 2 6 7 TC TCrows)
  exact ⟨htt, htc⟩

end ThreeCopyQutritWerner.X2.InK1x267
