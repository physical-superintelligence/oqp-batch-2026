module

public import ThreeCopyQutritWerner.CertificateX2InputU1x367x0

@[expose] public section


/-! S-pipeline T-tables of the type triple (3, 6, 7) of sector 1 and their specification (sigma * x2EmbedS at every label triple). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x367
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBT ub 9 17
x2_tt_gen TT UBT 9 17 6 0
x2_tt_gen TC UBT 9 17 6 1

theorem shape : ∀ a0 < x2Mult 1 3, ∀ a1 < x2Mult 1 6, ((UBT.getD a0 []).getD a1 []).length = x2Mult 1 3 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult 1 6 := by
  show ∀ a0 < 9, ∀ a1 < 17, ((UBT.getD a0 []).getD a1 []).length = 9 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = 17
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
  · exact ⟨(ubc_2_0).2.1, (ubc_2_0).2.2⟩
  · exact ⟨(ubc_2_1).2.1, (ubc_2_1).2.2⟩
  · exact ⟨(ubc_2_2).2.1, (ubc_2_2).2.2⟩
  · exact ⟨(ubc_2_3).2.1, (ubc_2_3).2.2⟩
  · exact ⟨(ubc_2_4).2.1, (ubc_2_4).2.2⟩
  · exact ⟨(ubc_2_5).2.1, (ubc_2_5).2.2⟩
  · exact ⟨(ubc_2_6).2.1, (ubc_2_6).2.2⟩
  · exact ⟨(ubc_2_7).2.1, (ubc_2_7).2.2⟩
  · exact ⟨(ubc_2_8).2.1, (ubc_2_8).2.2⟩
  · exact ⟨(ubc_2_9).2.1, (ubc_2_9).2.2⟩
  · exact ⟨(ubc_2_10).2.1, (ubc_2_10).2.2⟩
  · exact ⟨(ubc_2_11).2.1, (ubc_2_11).2.2⟩
  · exact ⟨(ubc_2_12).2.1, (ubc_2_12).2.2⟩
  · exact ⟨(ubc_2_13).2.1, (ubc_2_13).2.2⟩
  · exact ⟨(ubc_2_14).2.1, (ubc_2_14).2.2⟩
  · exact ⟨(ubc_2_15).2.1, (ubc_2_15).2.2⟩
  · exact ⟨(ubc_2_16).2.1, (ubc_2_16).2.2⟩
  · exact ⟨(ubc_3_0).2.1, (ubc_3_0).2.2⟩
  · exact ⟨(ubc_3_1).2.1, (ubc_3_1).2.2⟩
  · exact ⟨(ubc_3_2).2.1, (ubc_3_2).2.2⟩
  · exact ⟨(ubc_3_3).2.1, (ubc_3_3).2.2⟩
  · exact ⟨(ubc_3_4).2.1, (ubc_3_4).2.2⟩
  · exact ⟨(ubc_3_5).2.1, (ubc_3_5).2.2⟩
  · exact ⟨(ubc_3_6).2.1, (ubc_3_6).2.2⟩
  · exact ⟨(ubc_3_7).2.1, (ubc_3_7).2.2⟩
  · exact ⟨(ubc_3_8).2.1, (ubc_3_8).2.2⟩
  · exact ⟨(ubc_3_9).2.1, (ubc_3_9).2.2⟩
  · exact ⟨(ubc_3_10).2.1, (ubc_3_10).2.2⟩
  · exact ⟨(ubc_3_11).2.1, (ubc_3_11).2.2⟩
  · exact ⟨(ubc_3_12).2.1, (ubc_3_12).2.2⟩
  · exact ⟨(ubc_3_13).2.1, (ubc_3_13).2.2⟩
  · exact ⟨(ubc_3_14).2.1, (ubc_3_14).2.2⟩
  · exact ⟨(ubc_3_15).2.1, (ubc_3_15).2.2⟩
  · exact ⟨(ubc_3_16).2.1, (ubc_3_16).2.2⟩
  · exact ⟨(ubc_4_0).2.1, (ubc_4_0).2.2⟩
  · exact ⟨(ubc_4_1).2.1, (ubc_4_1).2.2⟩
  · exact ⟨(ubc_4_2).2.1, (ubc_4_2).2.2⟩
  · exact ⟨(ubc_4_3).2.1, (ubc_4_3).2.2⟩
  · exact ⟨(ubc_4_4).2.1, (ubc_4_4).2.2⟩
  · exact ⟨(ubc_4_5).2.1, (ubc_4_5).2.2⟩
  · exact ⟨(ubc_4_6).2.1, (ubc_4_6).2.2⟩
  · exact ⟨(ubc_4_7).2.1, (ubc_4_7).2.2⟩
  · exact ⟨(ubc_4_8).2.1, (ubc_4_8).2.2⟩
  · exact ⟨(ubc_4_9).2.1, (ubc_4_9).2.2⟩
  · exact ⟨(ubc_4_10).2.1, (ubc_4_10).2.2⟩
  · exact ⟨(ubc_4_11).2.1, (ubc_4_11).2.2⟩
  · exact ⟨(ubc_4_12).2.1, (ubc_4_12).2.2⟩
  · exact ⟨(ubc_4_13).2.1, (ubc_4_13).2.2⟩
  · exact ⟨(ubc_4_14).2.1, (ubc_4_14).2.2⟩
  · exact ⟨(ubc_4_15).2.1, (ubc_4_15).2.2⟩
  · exact ⟨(ubc_4_16).2.1, (ubc_4_16).2.2⟩
  · exact ⟨(ubc_5_0).2.1, (ubc_5_0).2.2⟩
  · exact ⟨(ubc_5_1).2.1, (ubc_5_1).2.2⟩
  · exact ⟨(ubc_5_2).2.1, (ubc_5_2).2.2⟩
  · exact ⟨(ubc_5_3).2.1, (ubc_5_3).2.2⟩
  · exact ⟨(ubc_5_4).2.1, (ubc_5_4).2.2⟩
  · exact ⟨(ubc_5_5).2.1, (ubc_5_5).2.2⟩
  · exact ⟨(ubc_5_6).2.1, (ubc_5_6).2.2⟩
  · exact ⟨(ubc_5_7).2.1, (ubc_5_7).2.2⟩
  · exact ⟨(ubc_5_8).2.1, (ubc_5_8).2.2⟩
  · exact ⟨(ubc_5_9).2.1, (ubc_5_9).2.2⟩
  · exact ⟨(ubc_5_10).2.1, (ubc_5_10).2.2⟩
  · exact ⟨(ubc_5_11).2.1, (ubc_5_11).2.2⟩
  · exact ⟨(ubc_5_12).2.1, (ubc_5_12).2.2⟩
  · exact ⟨(ubc_5_13).2.1, (ubc_5_13).2.2⟩
  · exact ⟨(ubc_5_14).2.1, (ubc_5_14).2.2⟩
  · exact ⟨(ubc_5_15).2.1, (ubc_5_15).2.2⟩
  · exact ⟨(ubc_5_16).2.1, (ubc_5_16).2.2⟩
  · exact ⟨(ubc_6_0).2.1, (ubc_6_0).2.2⟩
  · exact ⟨(ubc_6_1).2.1, (ubc_6_1).2.2⟩
  · exact ⟨(ubc_6_2).2.1, (ubc_6_2).2.2⟩
  · exact ⟨(ubc_6_3).2.1, (ubc_6_3).2.2⟩
  · exact ⟨(ubc_6_4).2.1, (ubc_6_4).2.2⟩
  · exact ⟨(ubc_6_5).2.1, (ubc_6_5).2.2⟩
  · exact ⟨(ubc_6_6).2.1, (ubc_6_6).2.2⟩
  · exact ⟨(ubc_6_7).2.1, (ubc_6_7).2.2⟩
  · exact ⟨(ubc_6_8).2.1, (ubc_6_8).2.2⟩
  · exact ⟨(ubc_6_9).2.1, (ubc_6_9).2.2⟩
  · exact ⟨(ubc_6_10).2.1, (ubc_6_10).2.2⟩
  · exact ⟨(ubc_6_11).2.1, (ubc_6_11).2.2⟩
  · exact ⟨(ubc_6_12).2.1, (ubc_6_12).2.2⟩
  · exact ⟨(ubc_6_13).2.1, (ubc_6_13).2.2⟩
  · exact ⟨(ubc_6_14).2.1, (ubc_6_14).2.2⟩
  · exact ⟨(ubc_6_15).2.1, (ubc_6_15).2.2⟩
  · exact ⟨(ubc_6_16).2.1, (ubc_6_16).2.2⟩
  · exact ⟨(ubc_7_0).2.1, (ubc_7_0).2.2⟩
  · exact ⟨(ubc_7_1).2.1, (ubc_7_1).2.2⟩
  · exact ⟨(ubc_7_2).2.1, (ubc_7_2).2.2⟩
  · exact ⟨(ubc_7_3).2.1, (ubc_7_3).2.2⟩
  · exact ⟨(ubc_7_4).2.1, (ubc_7_4).2.2⟩
  · exact ⟨(ubc_7_5).2.1, (ubc_7_5).2.2⟩
  · exact ⟨(ubc_7_6).2.1, (ubc_7_6).2.2⟩
  · exact ⟨(ubc_7_7).2.1, (ubc_7_7).2.2⟩
  · exact ⟨(ubc_7_8).2.1, (ubc_7_8).2.2⟩
  · exact ⟨(ubc_7_9).2.1, (ubc_7_9).2.2⟩
  · exact ⟨(ubc_7_10).2.1, (ubc_7_10).2.2⟩
  · exact ⟨(ubc_7_11).2.1, (ubc_7_11).2.2⟩
  · exact ⟨(ubc_7_12).2.1, (ubc_7_12).2.2⟩
  · exact ⟨(ubc_7_13).2.1, (ubc_7_13).2.2⟩
  · exact ⟨(ubc_7_14).2.1, (ubc_7_14).2.2⟩
  · exact ⟨(ubc_7_15).2.1, (ubc_7_15).2.2⟩
  · exact ⟨(ubc_7_16).2.1, (ubc_7_16).2.2⟩
  · exact ⟨(ubc_8_0).2.1, (ubc_8_0).2.2⟩
  · exact ⟨(ubc_8_1).2.1, (ubc_8_1).2.2⟩
  · exact ⟨(ubc_8_2).2.1, (ubc_8_2).2.2⟩
  · exact ⟨(ubc_8_3).2.1, (ubc_8_3).2.2⟩
  · exact ⟨(ubc_8_4).2.1, (ubc_8_4).2.2⟩
  · exact ⟨(ubc_8_5).2.1, (ubc_8_5).2.2⟩
  · exact ⟨(ubc_8_6).2.1, (ubc_8_6).2.2⟩
  · exact ⟨(ubc_8_7).2.1, (ubc_8_7).2.2⟩
  · exact ⟨(ubc_8_8).2.1, (ubc_8_8).2.2⟩
  · exact ⟨(ubc_8_9).2.1, (ubc_8_9).2.2⟩
  · exact ⟨(ubc_8_10).2.1, (ubc_8_10).2.2⟩
  · exact ⟨(ubc_8_11).2.1, (ubc_8_11).2.2⟩
  · exact ⟨(ubc_8_12).2.1, (ubc_8_12).2.2⟩
  · exact ⟨(ubc_8_13).2.1, (ubc_8_13).2.2⟩
  · exact ⟨(ubc_8_14).2.1, (ubc_8_14).2.2⟩
  · exact ⟨(ubc_8_15).2.1, (ubc_8_15).2.2⟩
  · exact ⟨(ubc_8_16).2.1, (ubc_8_16).2.2⟩
theorem hchk : ∀ a0 < x2Mult 1 3, ∀ a1 < x2Mult 1 6, ibBatchOK 256 (x2Mult 1 3 * x2Mult 1 6 * x2Mult 1 7) 302 (x2Mult 1 7) (x2Mult 1 3 * x2Mult 1 6) 0 (x2Mult 1 7) ((a0 * x2Mult 1 6 + a1) * x2Mult 1 7) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 9, ∀ a1 < 17, ibBatchOK 256 918 302 6 153 0 6 ((a0 * 17 + a1) * 6) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true
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
  · exact (ubc_2_0).1
  · exact (ubc_2_1).1
  · exact (ubc_2_2).1
  · exact (ubc_2_3).1
  · exact (ubc_2_4).1
  · exact (ubc_2_5).1
  · exact (ubc_2_6).1
  · exact (ubc_2_7).1
  · exact (ubc_2_8).1
  · exact (ubc_2_9).1
  · exact (ubc_2_10).1
  · exact (ubc_2_11).1
  · exact (ubc_2_12).1
  · exact (ubc_2_13).1
  · exact (ubc_2_14).1
  · exact (ubc_2_15).1
  · exact (ubc_2_16).1
  · exact (ubc_3_0).1
  · exact (ubc_3_1).1
  · exact (ubc_3_2).1
  · exact (ubc_3_3).1
  · exact (ubc_3_4).1
  · exact (ubc_3_5).1
  · exact (ubc_3_6).1
  · exact (ubc_3_7).1
  · exact (ubc_3_8).1
  · exact (ubc_3_9).1
  · exact (ubc_3_10).1
  · exact (ubc_3_11).1
  · exact (ubc_3_12).1
  · exact (ubc_3_13).1
  · exact (ubc_3_14).1
  · exact (ubc_3_15).1
  · exact (ubc_3_16).1
  · exact (ubc_4_0).1
  · exact (ubc_4_1).1
  · exact (ubc_4_2).1
  · exact (ubc_4_3).1
  · exact (ubc_4_4).1
  · exact (ubc_4_5).1
  · exact (ubc_4_6).1
  · exact (ubc_4_7).1
  · exact (ubc_4_8).1
  · exact (ubc_4_9).1
  · exact (ubc_4_10).1
  · exact (ubc_4_11).1
  · exact (ubc_4_12).1
  · exact (ubc_4_13).1
  · exact (ubc_4_14).1
  · exact (ubc_4_15).1
  · exact (ubc_4_16).1
  · exact (ubc_5_0).1
  · exact (ubc_5_1).1
  · exact (ubc_5_2).1
  · exact (ubc_5_3).1
  · exact (ubc_5_4).1
  · exact (ubc_5_5).1
  · exact (ubc_5_6).1
  · exact (ubc_5_7).1
  · exact (ubc_5_8).1
  · exact (ubc_5_9).1
  · exact (ubc_5_10).1
  · exact (ubc_5_11).1
  · exact (ubc_5_12).1
  · exact (ubc_5_13).1
  · exact (ubc_5_14).1
  · exact (ubc_5_15).1
  · exact (ubc_5_16).1
  · exact (ubc_6_0).1
  · exact (ubc_6_1).1
  · exact (ubc_6_2).1
  · exact (ubc_6_3).1
  · exact (ubc_6_4).1
  · exact (ubc_6_5).1
  · exact (ubc_6_6).1
  · exact (ubc_6_7).1
  · exact (ubc_6_8).1
  · exact (ubc_6_9).1
  · exact (ubc_6_10).1
  · exact (ubc_6_11).1
  · exact (ubc_6_12).1
  · exact (ubc_6_13).1
  · exact (ubc_6_14).1
  · exact (ubc_6_15).1
  · exact (ubc_6_16).1
  · exact (ubc_7_0).1
  · exact (ubc_7_1).1
  · exact (ubc_7_2).1
  · exact (ubc_7_3).1
  · exact (ubc_7_4).1
  · exact (ubc_7_5).1
  · exact (ubc_7_6).1
  · exact (ubc_7_7).1
  · exact (ubc_7_8).1
  · exact (ubc_7_9).1
  · exact (ubc_7_10).1
  · exact (ubc_7_11).1
  · exact (ubc_7_12).1
  · exact (ubc_7_13).1
  · exact (ubc_7_14).1
  · exact (ubc_7_15).1
  · exact (ubc_7_16).1
  · exact (ubc_8_0).1
  · exact (ubc_8_1).1
  · exact (ubc_8_2).1
  · exact (ubc_8_3).1
  · exact (ubc_8_4).1
  · exact (ubc_8_5).1
  · exact (ubc_8_6).1
  · exact (ubc_8_7).1
  · exact (ubc_8_8).1
  · exact (ubc_8_9).1
  · exact (ubc_8_10).1
  · exact (ubc_8_11).1
  · exact (ubc_8_12).1
  · exact (ubc_8_13).1
  · exact (ubc_8_14).1
  · exact (ubc_8_15).1
  · exact (ubc_8_16).1
theorem TTr_0 : (List.range 133).all (fun k => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 3)) ((pairsU (x2Mult 1 6)).getD (0 + k) (0, 0)) (TT.getD (0 + k) [])) = true := by decide +kernel
theorem TTr_133 : (List.range 20).all (fun k => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 3)) ((pairsU (x2Mult 1 6)).getD (133 + k) (0, 0)) (TT.getD (133 + k) [])) = true := by decide +kernel
theorem TTrows : ∀ i < nS 1 6, tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 3)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i []) = true := by
  show ∀ i < 153, tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 3)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i []) = true
  intro i hi
  rcases (by omega : (0 ≤ i ∧ i < 133) ∨ (133 ≤ i ∧ i < 153)) with h | h
  · exact rangeAll_sound (fun i => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 3)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i [])) 0 133 TTr_0 i h.1 (by omega)
  · exact rangeAll_sound (fun i => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 3)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i [])) 133 20 TTr_133 i h.1 (by omega)
theorem TCr_0 : (List.range 39).all (fun k => tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 3)).getD (0 + k) (0, 0)) (TC.getD (0 + k) [])) = true := by decide +kernel
theorem TCr_39 : (List.range 6).all (fun k => tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 3)).getD (39 + k) (0, 0)) (TC.getD (39 + k) [])) = true := by decide +kernel
theorem TCrows : ∀ i < nS 1 3, tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 3)).getD i (0, 0)) (TC.getD i []) = true := by
  show ∀ i < 45, tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 3)).getD i (0, 0)) (TC.getD i []) = true
  intro i hi
  rcases (by omega : (0 ≤ i ∧ i < 39) ∨ (39 ≤ i ∧ i < 45)) with h | h
  · exact rangeAll_sound (fun i => tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 3)).getD i (0, 0)) (TC.getD i [])) 0 39 TCr_0 i h.1 (by omega)
  · exact rangeAll_sound (fun i => tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 3)).getD i (0, 0)) (TC.getD i [])) 39 6 TCr_39 i h.1 (by omega)

theorem spec (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN126 : N k126 = x2TrialForm 1 k126) :
    TTspecS 1 N 3 6 7 TT ∧ TCspecS 1 N 3 6 7 TC := by
  have hk := keys N hN126
  have htt := tripleSpecS 1 (by decide) N hN 3 6 7 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TT.getD i1 []).getD i0 0) (tTT_of_rows 1 (by decide) UBT 3 6 7 TT TTrows)
  have htc := tripleSpecS 1 (by decide) N hN 3 6 7 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TC.getD i0 []).getD i1 0) (tTC_of_rows 1 (by decide) UBT 3 6 7 TC TCrows)
  exact ⟨htt, htc⟩

end ThreeCopyQutritWerner.X2.InK1x367
