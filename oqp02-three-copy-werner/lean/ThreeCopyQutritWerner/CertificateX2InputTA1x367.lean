module

public import ThreeCopyQutritWerner.CertificateX2InputU1x367x0
public import ThreeCopyQutritWerner.CertificateX2InputSegA

@[expose] public section


/-! A-pipeline T-tables of the type triple (3, 6, 7) of sector 1 (AAS rows by the second / first A label, SAA, ASA) and their specification. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x367
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBTa ub 9 17
x2_tt_genG TTa UBTa 9 17 6 0 1 1 6 2 2 6
x2_tt_genG TCa UBTa 9 17 6 1 1 1 6 2 2 6
x2_tt_genG TTs UBTa 9 17 6 0 0 1 6 6 2 2
x2_tt_genG TCs UBTa 9 17 6 1 1 0 6 2 6 2

theorem shapeA : ∀ a0 < x2Mult 1 3, ∀ a1 < x2Mult 1 6, ((UBTa.getD a0 []).getD a1 []).length = x2Mult 1 3 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = x2Mult 1 6 := by
  show ∀ a0 < 9, ∀ a1 < 17, ((UBTa.getD a0 []).getD a1 []).length = 9 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = 17
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
theorem hchkA : ∀ a0 < x2Mult 1 3, ∀ a1 < x2Mult 1 6, ibBatchOK 256 (x2Mult 1 3 * x2Mult 1 6 * x2Mult 1 7) 302 (x2Mult 1 7) (x2Mult 1 3 * x2Mult 1 6) 0 (x2Mult 1 7) ((a0 * x2Mult 1 6 + a1) * x2Mult 1 7) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 9, ∀ a1 < 17, ibBatchOK 256 918 302 6 153 0 6 ((a0 * 17 + a1) * 6) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true
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
theorem TTar_0 : (List.range 136).all (fun k => tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 6)).getD (0 + k) (0, 0)) (TTa.getD (0 + k) [])) = true := by decide +kernel
theorem TTarows : ∀ i < nA 1 6, tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTa.getD i []) = true := by
  show ∀ i < 136, tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTa.getD i [])) 0 136 TTar_0 i (Nat.zero_le i) (by omega)
theorem TCar_0 : (List.range 36).all (fun k => tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 3)).getD (0 + k) (0, 0)) (TCa.getD (0 + k) [])) = true := by decide +kernel
theorem TCarows : ∀ i < nA 1 3, tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TCa.getD i []) = true := by
  show ∀ i < 36, tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TCa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TCa.getD i [])) 0 36 TCar_0 i (Nat.zero_le i) (by omega)
theorem TTsr_0 : (List.range 133).all (fun k => tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 6)).getD (0 + k) (0, 0)) (TTs.getD (0 + k) [])) = true := by decide +kernel
theorem TTsr_133 : (List.range 3).all (fun k => tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 6)).getD (133 + k) (0, 0)) (TTs.getD (133 + k) [])) = true := by decide +kernel
theorem TTsrows : ∀ i < nA 1 6, tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTs.getD i []) = true := by
  show ∀ i < 136, tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTs.getD i []) = true
  intro i hi
  rcases (by omega : (0 ≤ i ∧ i < 133) ∨ (133 ≤ i ∧ i < 136)) with h | h
  · exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTs.getD i [])) 0 133 TTsr_0 i h.1 (by omega)
  · exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTs.getD i [])) 133 3 TTsr_133 i h.1 (by omega)
theorem TCsr_0 : (List.range 36).all (fun k => tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 3)).getD (0 + k) (0, 0)) (TCs.getD (0 + k) [])) = true := by decide +kernel
theorem TCsrows : ∀ i < nA 1 3, tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TCs.getD i []) = true := by
  show ∀ i < 36, tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TCs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TCs.getD i [])) 0 36 TCsr_0 i (Nat.zero_le i) (by omega)

theorem specA (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN126 : N k126 = x2TrialForm 1 k126) :
    TTspecAAS 1 N 3 6 7 TTa ∧ TCspecAAS 1 N 3 6 7 TCa ∧ TTspecSAA 1 N 3 6 7 TTs ∧ TCspecASA 1 N 3 6 7 TCs :=
  tripleSpecA 1 (by decide) N hN 3 6 7 (by decide) (by decide) ks hks hnd (keys N hN126) hlen UBTa shapeA hchkA TTa TCa TTs TCs
    (tTab_of_rowsG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 3)) (pairsA (x2Mult 1 6)) (nA 1 3) (nA 1 6) (pairsAOK_mult 1 (by decide) 3).1 TTa TTarows)
    (tTabC_of_rowsG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 3)) (pairsA (x2Mult 1 6)) (nA 1 3) (nA 1 6) (pairsAOK_mult 1 (by decide) 6).1 TCa TCarows)
    (tTab_of_rowsG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 3)) (pairsA (x2Mult 1 6)) (nS 1 3) (nA 1 6) (pairsOK_mult 1 (by decide) 3).1 TTs TTsrows)
    (tTabC_of_rowsG UBTa (nS 1 7) 6 2 6 2 (pairsA (x2Mult 1 3)) (pairsU (x2Mult 1 6)) (nA 1 3) (nS 1 6) (pairsOK_mult 1 (by decide) 6).1 TCs TCsrows)

end ThreeCopyQutritWerner.X2.InK1x367
