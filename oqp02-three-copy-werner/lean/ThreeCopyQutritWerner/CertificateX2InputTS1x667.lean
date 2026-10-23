module

public import ThreeCopyQutritWerner.CertificateX2InputU1x667x0

@[expose] public section


/-! S-pipeline T-tables of the type triple (6, 6, 7) of sector 1 and their specification (sigma * x2EmbedS at every label triple). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x667
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBT ub 17 17
x2_tt_gen TT UBT 17 17 6 0

theorem shape : ∀ a0 < x2Mult 1 6, ∀ a1 < x2Mult 1 6, ((UBT.getD a0 []).getD a1 []).length = x2Mult 1 6 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult 1 6 := by
  show ∀ a0 < 17, ∀ a1 < 17, ((UBT.getD a0 []).getD a1 []).length = 17 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = 17
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
  · exact ⟨(ubc_9_10).2.1, (ubc_9_10).2.2⟩
  · exact ⟨(ubc_9_11).2.1, (ubc_9_11).2.2⟩
  · exact ⟨(ubc_9_12).2.1, (ubc_9_12).2.2⟩
  · exact ⟨(ubc_9_13).2.1, (ubc_9_13).2.2⟩
  · exact ⟨(ubc_9_14).2.1, (ubc_9_14).2.2⟩
  · exact ⟨(ubc_9_15).2.1, (ubc_9_15).2.2⟩
  · exact ⟨(ubc_9_16).2.1, (ubc_9_16).2.2⟩
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
  · exact ⟨(ubc_10_10).2.1, (ubc_10_10).2.2⟩
  · exact ⟨(ubc_10_11).2.1, (ubc_10_11).2.2⟩
  · exact ⟨(ubc_10_12).2.1, (ubc_10_12).2.2⟩
  · exact ⟨(ubc_10_13).2.1, (ubc_10_13).2.2⟩
  · exact ⟨(ubc_10_14).2.1, (ubc_10_14).2.2⟩
  · exact ⟨(ubc_10_15).2.1, (ubc_10_15).2.2⟩
  · exact ⟨(ubc_10_16).2.1, (ubc_10_16).2.2⟩
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
  · exact ⟨(ubc_11_10).2.1, (ubc_11_10).2.2⟩
  · exact ⟨(ubc_11_11).2.1, (ubc_11_11).2.2⟩
  · exact ⟨(ubc_11_12).2.1, (ubc_11_12).2.2⟩
  · exact ⟨(ubc_11_13).2.1, (ubc_11_13).2.2⟩
  · exact ⟨(ubc_11_14).2.1, (ubc_11_14).2.2⟩
  · exact ⟨(ubc_11_15).2.1, (ubc_11_15).2.2⟩
  · exact ⟨(ubc_11_16).2.1, (ubc_11_16).2.2⟩
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
  · exact ⟨(ubc_12_10).2.1, (ubc_12_10).2.2⟩
  · exact ⟨(ubc_12_11).2.1, (ubc_12_11).2.2⟩
  · exact ⟨(ubc_12_12).2.1, (ubc_12_12).2.2⟩
  · exact ⟨(ubc_12_13).2.1, (ubc_12_13).2.2⟩
  · exact ⟨(ubc_12_14).2.1, (ubc_12_14).2.2⟩
  · exact ⟨(ubc_12_15).2.1, (ubc_12_15).2.2⟩
  · exact ⟨(ubc_12_16).2.1, (ubc_12_16).2.2⟩
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
  · exact ⟨(ubc_13_10).2.1, (ubc_13_10).2.2⟩
  · exact ⟨(ubc_13_11).2.1, (ubc_13_11).2.2⟩
  · exact ⟨(ubc_13_12).2.1, (ubc_13_12).2.2⟩
  · exact ⟨(ubc_13_13).2.1, (ubc_13_13).2.2⟩
  · exact ⟨(ubc_13_14).2.1, (ubc_13_14).2.2⟩
  · exact ⟨(ubc_13_15).2.1, (ubc_13_15).2.2⟩
  · exact ⟨(ubc_13_16).2.1, (ubc_13_16).2.2⟩
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
  · exact ⟨(ubc_14_10).2.1, (ubc_14_10).2.2⟩
  · exact ⟨(ubc_14_11).2.1, (ubc_14_11).2.2⟩
  · exact ⟨(ubc_14_12).2.1, (ubc_14_12).2.2⟩
  · exact ⟨(ubc_14_13).2.1, (ubc_14_13).2.2⟩
  · exact ⟨(ubc_14_14).2.1, (ubc_14_14).2.2⟩
  · exact ⟨(ubc_14_15).2.1, (ubc_14_15).2.2⟩
  · exact ⟨(ubc_14_16).2.1, (ubc_14_16).2.2⟩
  · exact ⟨(ubc_15_0).2.1, (ubc_15_0).2.2⟩
  · exact ⟨(ubc_15_1).2.1, (ubc_15_1).2.2⟩
  · exact ⟨(ubc_15_2).2.1, (ubc_15_2).2.2⟩
  · exact ⟨(ubc_15_3).2.1, (ubc_15_3).2.2⟩
  · exact ⟨(ubc_15_4).2.1, (ubc_15_4).2.2⟩
  · exact ⟨(ubc_15_5).2.1, (ubc_15_5).2.2⟩
  · exact ⟨(ubc_15_6).2.1, (ubc_15_6).2.2⟩
  · exact ⟨(ubc_15_7).2.1, (ubc_15_7).2.2⟩
  · exact ⟨(ubc_15_8).2.1, (ubc_15_8).2.2⟩
  · exact ⟨(ubc_15_9).2.1, (ubc_15_9).2.2⟩
  · exact ⟨(ubc_15_10).2.1, (ubc_15_10).2.2⟩
  · exact ⟨(ubc_15_11).2.1, (ubc_15_11).2.2⟩
  · exact ⟨(ubc_15_12).2.1, (ubc_15_12).2.2⟩
  · exact ⟨(ubc_15_13).2.1, (ubc_15_13).2.2⟩
  · exact ⟨(ubc_15_14).2.1, (ubc_15_14).2.2⟩
  · exact ⟨(ubc_15_15).2.1, (ubc_15_15).2.2⟩
  · exact ⟨(ubc_15_16).2.1, (ubc_15_16).2.2⟩
  · exact ⟨(ubc_16_0).2.1, (ubc_16_0).2.2⟩
  · exact ⟨(ubc_16_1).2.1, (ubc_16_1).2.2⟩
  · exact ⟨(ubc_16_2).2.1, (ubc_16_2).2.2⟩
  · exact ⟨(ubc_16_3).2.1, (ubc_16_3).2.2⟩
  · exact ⟨(ubc_16_4).2.1, (ubc_16_4).2.2⟩
  · exact ⟨(ubc_16_5).2.1, (ubc_16_5).2.2⟩
  · exact ⟨(ubc_16_6).2.1, (ubc_16_6).2.2⟩
  · exact ⟨(ubc_16_7).2.1, (ubc_16_7).2.2⟩
  · exact ⟨(ubc_16_8).2.1, (ubc_16_8).2.2⟩
  · exact ⟨(ubc_16_9).2.1, (ubc_16_9).2.2⟩
  · exact ⟨(ubc_16_10).2.1, (ubc_16_10).2.2⟩
  · exact ⟨(ubc_16_11).2.1, (ubc_16_11).2.2⟩
  · exact ⟨(ubc_16_12).2.1, (ubc_16_12).2.2⟩
  · exact ⟨(ubc_16_13).2.1, (ubc_16_13).2.2⟩
  · exact ⟨(ubc_16_14).2.1, (ubc_16_14).2.2⟩
  · exact ⟨(ubc_16_15).2.1, (ubc_16_15).2.2⟩
  · exact ⟨(ubc_16_16).2.1, (ubc_16_16).2.2⟩
theorem hchk : ∀ a0 < x2Mult 1 6, ∀ a1 < x2Mult 1 6, ibBatchOK 256 (x2Mult 1 6 * x2Mult 1 6 * x2Mult 1 7) 302 (x2Mult 1 7) (x2Mult 1 6 * x2Mult 1 6) 0 (x2Mult 1 7) ((a0 * x2Mult 1 6 + a1) * x2Mult 1 7) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 17, ∀ a1 < 17, ibBatchOK 256 1734 302 6 289 0 6 ((a0 * 17 + a1) * 6) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true
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
  · exact (ubc_9_10).1
  · exact (ubc_9_11).1
  · exact (ubc_9_12).1
  · exact (ubc_9_13).1
  · exact (ubc_9_14).1
  · exact (ubc_9_15).1
  · exact (ubc_9_16).1
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
  · exact (ubc_10_10).1
  · exact (ubc_10_11).1
  · exact (ubc_10_12).1
  · exact (ubc_10_13).1
  · exact (ubc_10_14).1
  · exact (ubc_10_15).1
  · exact (ubc_10_16).1
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
  · exact (ubc_11_10).1
  · exact (ubc_11_11).1
  · exact (ubc_11_12).1
  · exact (ubc_11_13).1
  · exact (ubc_11_14).1
  · exact (ubc_11_15).1
  · exact (ubc_11_16).1
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
  · exact (ubc_12_10).1
  · exact (ubc_12_11).1
  · exact (ubc_12_12).1
  · exact (ubc_12_13).1
  · exact (ubc_12_14).1
  · exact (ubc_12_15).1
  · exact (ubc_12_16).1
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
  · exact (ubc_13_10).1
  · exact (ubc_13_11).1
  · exact (ubc_13_12).1
  · exact (ubc_13_13).1
  · exact (ubc_13_14).1
  · exact (ubc_13_15).1
  · exact (ubc_13_16).1
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
  · exact (ubc_14_10).1
  · exact (ubc_14_11).1
  · exact (ubc_14_12).1
  · exact (ubc_14_13).1
  · exact (ubc_14_14).1
  · exact (ubc_14_15).1
  · exact (ubc_14_16).1
  · exact (ubc_15_0).1
  · exact (ubc_15_1).1
  · exact (ubc_15_2).1
  · exact (ubc_15_3).1
  · exact (ubc_15_4).1
  · exact (ubc_15_5).1
  · exact (ubc_15_6).1
  · exact (ubc_15_7).1
  · exact (ubc_15_8).1
  · exact (ubc_15_9).1
  · exact (ubc_15_10).1
  · exact (ubc_15_11).1
  · exact (ubc_15_12).1
  · exact (ubc_15_13).1
  · exact (ubc_15_14).1
  · exact (ubc_15_15).1
  · exact (ubc_15_16).1
  · exact (ubc_16_0).1
  · exact (ubc_16_1).1
  · exact (ubc_16_2).1
  · exact (ubc_16_3).1
  · exact (ubc_16_4).1
  · exact (ubc_16_5).1
  · exact (ubc_16_6).1
  · exact (ubc_16_7).1
  · exact (ubc_16_8).1
  · exact (ubc_16_9).1
  · exact (ubc_16_10).1
  · exact (ubc_16_11).1
  · exact (ubc_16_12).1
  · exact (ubc_16_13).1
  · exact (ubc_16_14).1
  · exact (ubc_16_15).1
  · exact (ubc_16_16).1
theorem TTr_0 : (List.range 39).all (fun k => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD (0 + k) (0, 0)) (TT.getD (0 + k) [])) = true := by decide +kernel
theorem TTr_39 : (List.range 39).all (fun k => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD (39 + k) (0, 0)) (TT.getD (39 + k) [])) = true := by decide +kernel
theorem TTr_78 : (List.range 39).all (fun k => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD (78 + k) (0, 0)) (TT.getD (78 + k) [])) = true := by decide +kernel
theorem TTr_117 : (List.range 36).all (fun k => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD (117 + k) (0, 0)) (TT.getD (117 + k) [])) = true := by decide +kernel
theorem TTrows : ∀ i < nS 1 6, tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i []) = true := by
  show ∀ i < 153, tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i []) = true
  intro i hi
  rcases (by omega : (0 ≤ i ∧ i < 39) ∨ (39 ≤ i ∧ i < 78) ∨ (78 ≤ i ∧ i < 117) ∨ (117 ≤ i ∧ i < 153)) with h | h | h | h
  · exact rangeAll_sound (fun i => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i [])) 0 39 TTr_0 i h.1 (by omega)
  · exact rangeAll_sound (fun i => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i [])) 39 39 TTr_39 i h.1 (by omega)
  · exact rangeAll_sound (fun i => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i [])) 78 39 TTr_78 i h.1 (by omega)
  · exact rangeAll_sound (fun i => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 6)) ((pairsU (x2Mult 1 6)).getD i (0, 0)) (TT.getD i [])) 117 36 TTr_117 i h.1 (by omega)

theorem spec (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN162 : N k162 = x2TrialForm 1 k162) (hN163 : N k163 = x2TrialForm 1 k163) :
    TTspecS 1 N 6 6 7 TT ∧ TCspecS 1 N 6 6 7 TT := by
  have hk := keys N hN162 hN163
  have htt := tripleSpecS 1 (by decide) N hN 6 6 7 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TT.getD i1 []).getD i0 0) (tTT_of_rows 1 (by decide) UBT 6 6 7 TT TTrows)
  exact ⟨htt, tcSpec_of_tt_eq 1 N 6 7 TT htt⟩

end ThreeCopyQutritWerner.X2.InK1x667
