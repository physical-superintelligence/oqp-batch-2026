module

public import ThreeCopyQutritWerner.CertificateX2InputU2x456x0
public import ThreeCopyQutritWerner.CertificateX2InputSegA

@[expose] public section


/-! A-pipeline T-tables of the type triple (4, 5, 6) of sector 2 (AAS rows by the second / first A label, SAA, ASA) and their specification. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x456
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBTa ub 15 10
x2_tt_genG TTa UBTa 15 10 11 0 1 1 6 2 2 6
x2_tt_genG TCa UBTa 15 10 11 1 1 1 6 2 2 6
x2_tt_genG TTs UBTa 15 10 11 0 0 1 6 6 2 2
x2_tt_genG TCs UBTa 15 10 11 1 1 0 6 2 6 2

theorem shapeA : ∀ a0 < x2Mult 2 4, ∀ a1 < x2Mult 2 5, ((UBTa.getD a0 []).getD a1 []).length = x2Mult 2 4 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = x2Mult 2 5 := by
  show ∀ a0 < 15, ∀ a1 < 10, ((UBTa.getD a0 []).getD a1 []).length = 15 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = 10
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
  · exact ⟨(ubc_9_0).2.1, (ubc_9_0).2.2⟩
  · exact ⟨(ubc_9_1).2.1, (ubc_9_1).2.2⟩
  · exact ⟨(ubc_9_2).2.1, (ubc_9_2).2.2⟩
  · exact ⟨(ubc_9_3).2.1, (ubc_9_3).2.2⟩
  · exact ⟨(ubc_9_4).2.1, (ubc_9_4).2.2⟩
  · exact ⟨(ubc_9_5).2.1, (ubc_9_5).2.2⟩
  · exact ⟨(ubc_9_6).2.1, (ubc_9_6).2.2⟩
  · exact ⟨(ubc_9_7).2.1, (ubc_9_7).2.2⟩
  · exact ⟨(ubc_9_8).2.1, (ubc_9_8).2.2⟩
  · exact ⟨(ubc_9_9).2.1, (ubc_9_9).2.2⟩
  · exact ⟨(ubc_10_0).2.1, (ubc_10_0).2.2⟩
  · exact ⟨(ubc_10_1).2.1, (ubc_10_1).2.2⟩
  · exact ⟨(ubc_10_2).2.1, (ubc_10_2).2.2⟩
  · exact ⟨(ubc_10_3).2.1, (ubc_10_3).2.2⟩
  · exact ⟨(ubc_10_4).2.1, (ubc_10_4).2.2⟩
  · exact ⟨(ubc_10_5).2.1, (ubc_10_5).2.2⟩
  · exact ⟨(ubc_10_6).2.1, (ubc_10_6).2.2⟩
  · exact ⟨(ubc_10_7).2.1, (ubc_10_7).2.2⟩
  · exact ⟨(ubc_10_8).2.1, (ubc_10_8).2.2⟩
  · exact ⟨(ubc_10_9).2.1, (ubc_10_9).2.2⟩
  · exact ⟨(ubc_11_0).2.1, (ubc_11_0).2.2⟩
  · exact ⟨(ubc_11_1).2.1, (ubc_11_1).2.2⟩
  · exact ⟨(ubc_11_2).2.1, (ubc_11_2).2.2⟩
  · exact ⟨(ubc_11_3).2.1, (ubc_11_3).2.2⟩
  · exact ⟨(ubc_11_4).2.1, (ubc_11_4).2.2⟩
  · exact ⟨(ubc_11_5).2.1, (ubc_11_5).2.2⟩
  · exact ⟨(ubc_11_6).2.1, (ubc_11_6).2.2⟩
  · exact ⟨(ubc_11_7).2.1, (ubc_11_7).2.2⟩
  · exact ⟨(ubc_11_8).2.1, (ubc_11_8).2.2⟩
  · exact ⟨(ubc_11_9).2.1, (ubc_11_9).2.2⟩
  · exact ⟨(ubc_12_0).2.1, (ubc_12_0).2.2⟩
  · exact ⟨(ubc_12_1).2.1, (ubc_12_1).2.2⟩
  · exact ⟨(ubc_12_2).2.1, (ubc_12_2).2.2⟩
  · exact ⟨(ubc_12_3).2.1, (ubc_12_3).2.2⟩
  · exact ⟨(ubc_12_4).2.1, (ubc_12_4).2.2⟩
  · exact ⟨(ubc_12_5).2.1, (ubc_12_5).2.2⟩
  · exact ⟨(ubc_12_6).2.1, (ubc_12_6).2.2⟩
  · exact ⟨(ubc_12_7).2.1, (ubc_12_7).2.2⟩
  · exact ⟨(ubc_12_8).2.1, (ubc_12_8).2.2⟩
  · exact ⟨(ubc_12_9).2.1, (ubc_12_9).2.2⟩
  · exact ⟨(ubc_13_0).2.1, (ubc_13_0).2.2⟩
  · exact ⟨(ubc_13_1).2.1, (ubc_13_1).2.2⟩
  · exact ⟨(ubc_13_2).2.1, (ubc_13_2).2.2⟩
  · exact ⟨(ubc_13_3).2.1, (ubc_13_3).2.2⟩
  · exact ⟨(ubc_13_4).2.1, (ubc_13_4).2.2⟩
  · exact ⟨(ubc_13_5).2.1, (ubc_13_5).2.2⟩
  · exact ⟨(ubc_13_6).2.1, (ubc_13_6).2.2⟩
  · exact ⟨(ubc_13_7).2.1, (ubc_13_7).2.2⟩
  · exact ⟨(ubc_13_8).2.1, (ubc_13_8).2.2⟩
  · exact ⟨(ubc_13_9).2.1, (ubc_13_9).2.2⟩
  · exact ⟨(ubc_14_0).2.1, (ubc_14_0).2.2⟩
  · exact ⟨(ubc_14_1).2.1, (ubc_14_1).2.2⟩
  · exact ⟨(ubc_14_2).2.1, (ubc_14_2).2.2⟩
  · exact ⟨(ubc_14_3).2.1, (ubc_14_3).2.2⟩
  · exact ⟨(ubc_14_4).2.1, (ubc_14_4).2.2⟩
  · exact ⟨(ubc_14_5).2.1, (ubc_14_5).2.2⟩
  · exact ⟨(ubc_14_6).2.1, (ubc_14_6).2.2⟩
  · exact ⟨(ubc_14_7).2.1, (ubc_14_7).2.2⟩
  · exact ⟨(ubc_14_8).2.1, (ubc_14_8).2.2⟩
  · exact ⟨(ubc_14_9).2.1, (ubc_14_9).2.2⟩
theorem hchkA : ∀ a0 < x2Mult 2 4, ∀ a1 < x2Mult 2 5, ibBatchOK 256 (x2Mult 2 4 * x2Mult 2 5 * x2Mult 2 6) 302 (x2Mult 2 6) (x2Mult 2 4 * x2Mult 2 5) 0 (x2Mult 2 6) ((a0 * x2Mult 2 5 + a1) * x2Mult 2 6) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 15, ∀ a1 < 10, ibBatchOK 256 1650 302 11 150 0 11 ((a0 * 10 + a1) * 11) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true
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
  · exact (ubc_9_0).1
  · exact (ubc_9_1).1
  · exact (ubc_9_2).1
  · exact (ubc_9_3).1
  · exact (ubc_9_4).1
  · exact (ubc_9_5).1
  · exact (ubc_9_6).1
  · exact (ubc_9_7).1
  · exact (ubc_9_8).1
  · exact (ubc_9_9).1
  · exact (ubc_10_0).1
  · exact (ubc_10_1).1
  · exact (ubc_10_2).1
  · exact (ubc_10_3).1
  · exact (ubc_10_4).1
  · exact (ubc_10_5).1
  · exact (ubc_10_6).1
  · exact (ubc_10_7).1
  · exact (ubc_10_8).1
  · exact (ubc_10_9).1
  · exact (ubc_11_0).1
  · exact (ubc_11_1).1
  · exact (ubc_11_2).1
  · exact (ubc_11_3).1
  · exact (ubc_11_4).1
  · exact (ubc_11_5).1
  · exact (ubc_11_6).1
  · exact (ubc_11_7).1
  · exact (ubc_11_8).1
  · exact (ubc_11_9).1
  · exact (ubc_12_0).1
  · exact (ubc_12_1).1
  · exact (ubc_12_2).1
  · exact (ubc_12_3).1
  · exact (ubc_12_4).1
  · exact (ubc_12_5).1
  · exact (ubc_12_6).1
  · exact (ubc_12_7).1
  · exact (ubc_12_8).1
  · exact (ubc_12_9).1
  · exact (ubc_13_0).1
  · exact (ubc_13_1).1
  · exact (ubc_13_2).1
  · exact (ubc_13_3).1
  · exact (ubc_13_4).1
  · exact (ubc_13_5).1
  · exact (ubc_13_6).1
  · exact (ubc_13_7).1
  · exact (ubc_13_8).1
  · exact (ubc_13_9).1
  · exact (ubc_14_0).1
  · exact (ubc_14_1).1
  · exact (ubc_14_2).1
  · exact (ubc_14_3).1
  · exact (ubc_14_4).1
  · exact (ubc_14_5).1
  · exact (ubc_14_6).1
  · exact (ubc_14_7).1
  · exact (ubc_14_8).1
  · exact (ubc_14_9).1
theorem TTar_0 : (List.range 45).all (fun k => tRowOKG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 4)) ((pairsA (x2Mult 2 5)).getD (0 + k) (0, 0)) (TTa.getD (0 + k) [])) = true := by decide +kernel
theorem TTarows : ∀ i < nA 2 5, tRowOKG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 4)) ((pairsA (x2Mult 2 5)).getD i (0, 0)) (TTa.getD i []) = true := by
  show ∀ i < 45, tRowOKG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 4)) ((pairsA (x2Mult 2 5)).getD i (0, 0)) (TTa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 4)) ((pairsA (x2Mult 2 5)).getD i (0, 0)) (TTa.getD i [])) 0 45 TTar_0 i (Nat.zero_le i) (by omega)
theorem TCar_0 : (List.range 105).all (fun k => tRowOKG' UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 5)) ((pairsA (x2Mult 2 4)).getD (0 + k) (0, 0)) (TCa.getD (0 + k) [])) = true := by decide +kernel
theorem TCarows : ∀ i < nA 2 4, tRowOKG' UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 5)) ((pairsA (x2Mult 2 4)).getD i (0, 0)) (TCa.getD i []) = true := by
  show ∀ i < 105, tRowOKG' UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 5)) ((pairsA (x2Mult 2 4)).getD i (0, 0)) (TCa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 5)) ((pairsA (x2Mult 2 4)).getD i (0, 0)) (TCa.getD i [])) 0 105 TCar_0 i (Nat.zero_le i) (by omega)
theorem TTsr_0 : (List.range 45).all (fun k => tRowOKG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 4)) ((pairsA (x2Mult 2 5)).getD (0 + k) (0, 0)) (TTs.getD (0 + k) [])) = true := by decide +kernel
theorem TTsrows : ∀ i < nA 2 5, tRowOKG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 4)) ((pairsA (x2Mult 2 5)).getD i (0, 0)) (TTs.getD i []) = true := by
  show ∀ i < 45, tRowOKG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 4)) ((pairsA (x2Mult 2 5)).getD i (0, 0)) (TTs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 4)) ((pairsA (x2Mult 2 5)).getD i (0, 0)) (TTs.getD i [])) 0 45 TTsr_0 i (Nat.zero_le i) (by omega)
theorem TCsr_0 : (List.range 105).all (fun k => tRowOKG' UBTa (nS 2 6) 6 2 6 2 (pairsU (x2Mult 2 5)) ((pairsA (x2Mult 2 4)).getD (0 + k) (0, 0)) (TCs.getD (0 + k) [])) = true := by decide +kernel
theorem TCsrows : ∀ i < nA 2 4, tRowOKG' UBTa (nS 2 6) 6 2 6 2 (pairsU (x2Mult 2 5)) ((pairsA (x2Mult 2 4)).getD i (0, 0)) (TCs.getD i []) = true := by
  show ∀ i < 105, tRowOKG' UBTa (nS 2 6) 6 2 6 2 (pairsU (x2Mult 2 5)) ((pairsA (x2Mult 2 4)).getD i (0, 0)) (TCs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 2 6) 6 2 6 2 (pairsU (x2Mult 2 5)) ((pairsA (x2Mult 2 4)).getD i (0, 0)) (TCs.getD i [])) 0 105 TCsr_0 i (Nat.zero_le i) (by omega)

theorem specA (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN110 : N k110 = x2TrialForm 2 k110) :
    TTspecAAS 2 N 4 5 6 TTa ∧ TCspecAAS 2 N 4 5 6 TCa ∧ TTspecSAA 2 N 4 5 6 TTs ∧ TCspecASA 2 N 4 5 6 TCs :=
  tripleSpecA 2 (by decide) N hN 4 5 6 (by decide) (by decide) ks hks hnd (keys N hN110) hlen UBTa shapeA hchkA TTa TCa TTs TCs
    (tTab_of_rowsG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 4)) (pairsA (x2Mult 2 5)) (nA 2 4) (nA 2 5) (pairsAOK_mult 2 (by decide) 4).1 TTa TTarows)
    (tTabC_of_rowsG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 4)) (pairsA (x2Mult 2 5)) (nA 2 4) (nA 2 5) (pairsAOK_mult 2 (by decide) 5).1 TCa TCarows)
    (tTab_of_rowsG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 4)) (pairsA (x2Mult 2 5)) (nS 2 4) (nA 2 5) (pairsOK_mult 2 (by decide) 4).1 TTs TTsrows)
    (tTabC_of_rowsG UBTa (nS 2 6) 6 2 6 2 (pairsA (x2Mult 2 4)) (pairsU (x2Mult 2 5)) (nA 2 4) (nS 2 5) (pairsOK_mult 2 (by decide) 5).1 TCs TCsrows)

end ThreeCopyQutritWerner.X2.InK2x456
