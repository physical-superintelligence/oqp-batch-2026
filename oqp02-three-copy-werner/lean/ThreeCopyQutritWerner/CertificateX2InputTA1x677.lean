module

public import ThreeCopyQutritWerner.CertificateX2InputU1x677x0
public import ThreeCopyQutritWerner.CertificateX2InputSegA

@[expose] public section


/-! A-pipeline T-tables of the type triple (6, 7, 7) of sector 1 (AAS rows by the second / first A label, SAA, ASA) and their specification. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x677
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBTa ub 17 6
x2_tt_genG TTa UBTa 17 6 6 0 1 1 6 2 2 6
x2_tt_genG TCa UBTa 17 6 6 1 1 1 6 2 2 6
x2_tt_genG TTs UBTa 17 6 6 0 0 1 6 6 2 2
x2_tt_genG TCs UBTa 17 6 6 1 1 0 6 2 6 2

theorem shapeA : ∀ a0 < x2Mult 1 6, ∀ a1 < x2Mult 1 7, ((UBTa.getD a0 []).getD a1 []).length = x2Mult 1 6 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = x2Mult 1 7 := by
  show ∀ a0 < 17, ∀ a1 < 6, ((UBTa.getD a0 []).getD a1 []).length = 17 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = 6
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact ⟨(ubc_0_0).2.1, (ubc_0_0).2.2⟩
  · exact ⟨(ubc_0_1).2.1, (ubc_0_1).2.2⟩
  · exact ⟨(ubc_0_2).2.1, (ubc_0_2).2.2⟩
  · exact ⟨(ubc_0_3).2.1, (ubc_0_3).2.2⟩
  · exact ⟨(ubc_0_4).2.1, (ubc_0_4).2.2⟩
  · exact ⟨(ubc_0_5).2.1, (ubc_0_5).2.2⟩
  · exact ⟨(ubc_1_0).2.1, (ubc_1_0).2.2⟩
  · exact ⟨(ubc_1_1).2.1, (ubc_1_1).2.2⟩
  · exact ⟨(ubc_1_2).2.1, (ubc_1_2).2.2⟩
  · exact ⟨(ubc_1_3).2.1, (ubc_1_3).2.2⟩
  · exact ⟨(ubc_1_4).2.1, (ubc_1_4).2.2⟩
  · exact ⟨(ubc_1_5).2.1, (ubc_1_5).2.2⟩
  · exact ⟨(ubc_2_0).2.1, (ubc_2_0).2.2⟩
  · exact ⟨(ubc_2_1).2.1, (ubc_2_1).2.2⟩
  · exact ⟨(ubc_2_2).2.1, (ubc_2_2).2.2⟩
  · exact ⟨(ubc_2_3).2.1, (ubc_2_3).2.2⟩
  · exact ⟨(ubc_2_4).2.1, (ubc_2_4).2.2⟩
  · exact ⟨(ubc_2_5).2.1, (ubc_2_5).2.2⟩
  · exact ⟨(ubc_3_0).2.1, (ubc_3_0).2.2⟩
  · exact ⟨(ubc_3_1).2.1, (ubc_3_1).2.2⟩
  · exact ⟨(ubc_3_2).2.1, (ubc_3_2).2.2⟩
  · exact ⟨(ubc_3_3).2.1, (ubc_3_3).2.2⟩
  · exact ⟨(ubc_3_4).2.1, (ubc_3_4).2.2⟩
  · exact ⟨(ubc_3_5).2.1, (ubc_3_5).2.2⟩
  · exact ⟨(ubc_4_0).2.1, (ubc_4_0).2.2⟩
  · exact ⟨(ubc_4_1).2.1, (ubc_4_1).2.2⟩
  · exact ⟨(ubc_4_2).2.1, (ubc_4_2).2.2⟩
  · exact ⟨(ubc_4_3).2.1, (ubc_4_3).2.2⟩
  · exact ⟨(ubc_4_4).2.1, (ubc_4_4).2.2⟩
  · exact ⟨(ubc_4_5).2.1, (ubc_4_5).2.2⟩
  · exact ⟨(ubc_5_0).2.1, (ubc_5_0).2.2⟩
  · exact ⟨(ubc_5_1).2.1, (ubc_5_1).2.2⟩
  · exact ⟨(ubc_5_2).2.1, (ubc_5_2).2.2⟩
  · exact ⟨(ubc_5_3).2.1, (ubc_5_3).2.2⟩
  · exact ⟨(ubc_5_4).2.1, (ubc_5_4).2.2⟩
  · exact ⟨(ubc_5_5).2.1, (ubc_5_5).2.2⟩
  · exact ⟨(ubc_6_0).2.1, (ubc_6_0).2.2⟩
  · exact ⟨(ubc_6_1).2.1, (ubc_6_1).2.2⟩
  · exact ⟨(ubc_6_2).2.1, (ubc_6_2).2.2⟩
  · exact ⟨(ubc_6_3).2.1, (ubc_6_3).2.2⟩
  · exact ⟨(ubc_6_4).2.1, (ubc_6_4).2.2⟩
  · exact ⟨(ubc_6_5).2.1, (ubc_6_5).2.2⟩
  · exact ⟨(ubc_7_0).2.1, (ubc_7_0).2.2⟩
  · exact ⟨(ubc_7_1).2.1, (ubc_7_1).2.2⟩
  · exact ⟨(ubc_7_2).2.1, (ubc_7_2).2.2⟩
  · exact ⟨(ubc_7_3).2.1, (ubc_7_3).2.2⟩
  · exact ⟨(ubc_7_4).2.1, (ubc_7_4).2.2⟩
  · exact ⟨(ubc_7_5).2.1, (ubc_7_5).2.2⟩
  · exact ⟨(ubc_8_0).2.1, (ubc_8_0).2.2⟩
  · exact ⟨(ubc_8_1).2.1, (ubc_8_1).2.2⟩
  · exact ⟨(ubc_8_2).2.1, (ubc_8_2).2.2⟩
  · exact ⟨(ubc_8_3).2.1, (ubc_8_3).2.2⟩
  · exact ⟨(ubc_8_4).2.1, (ubc_8_4).2.2⟩
  · exact ⟨(ubc_8_5).2.1, (ubc_8_5).2.2⟩
  · exact ⟨(ubc_9_0).2.1, (ubc_9_0).2.2⟩
  · exact ⟨(ubc_9_1).2.1, (ubc_9_1).2.2⟩
  · exact ⟨(ubc_9_2).2.1, (ubc_9_2).2.2⟩
  · exact ⟨(ubc_9_3).2.1, (ubc_9_3).2.2⟩
  · exact ⟨(ubc_9_4).2.1, (ubc_9_4).2.2⟩
  · exact ⟨(ubc_9_5).2.1, (ubc_9_5).2.2⟩
  · exact ⟨(ubc_10_0).2.1, (ubc_10_0).2.2⟩
  · exact ⟨(ubc_10_1).2.1, (ubc_10_1).2.2⟩
  · exact ⟨(ubc_10_2).2.1, (ubc_10_2).2.2⟩
  · exact ⟨(ubc_10_3).2.1, (ubc_10_3).2.2⟩
  · exact ⟨(ubc_10_4).2.1, (ubc_10_4).2.2⟩
  · exact ⟨(ubc_10_5).2.1, (ubc_10_5).2.2⟩
  · exact ⟨(ubc_11_0).2.1, (ubc_11_0).2.2⟩
  · exact ⟨(ubc_11_1).2.1, (ubc_11_1).2.2⟩
  · exact ⟨(ubc_11_2).2.1, (ubc_11_2).2.2⟩
  · exact ⟨(ubc_11_3).2.1, (ubc_11_3).2.2⟩
  · exact ⟨(ubc_11_4).2.1, (ubc_11_4).2.2⟩
  · exact ⟨(ubc_11_5).2.1, (ubc_11_5).2.2⟩
  · exact ⟨(ubc_12_0).2.1, (ubc_12_0).2.2⟩
  · exact ⟨(ubc_12_1).2.1, (ubc_12_1).2.2⟩
  · exact ⟨(ubc_12_2).2.1, (ubc_12_2).2.2⟩
  · exact ⟨(ubc_12_3).2.1, (ubc_12_3).2.2⟩
  · exact ⟨(ubc_12_4).2.1, (ubc_12_4).2.2⟩
  · exact ⟨(ubc_12_5).2.1, (ubc_12_5).2.2⟩
  · exact ⟨(ubc_13_0).2.1, (ubc_13_0).2.2⟩
  · exact ⟨(ubc_13_1).2.1, (ubc_13_1).2.2⟩
  · exact ⟨(ubc_13_2).2.1, (ubc_13_2).2.2⟩
  · exact ⟨(ubc_13_3).2.1, (ubc_13_3).2.2⟩
  · exact ⟨(ubc_13_4).2.1, (ubc_13_4).2.2⟩
  · exact ⟨(ubc_13_5).2.1, (ubc_13_5).2.2⟩
  · exact ⟨(ubc_14_0).2.1, (ubc_14_0).2.2⟩
  · exact ⟨(ubc_14_1).2.1, (ubc_14_1).2.2⟩
  · exact ⟨(ubc_14_2).2.1, (ubc_14_2).2.2⟩
  · exact ⟨(ubc_14_3).2.1, (ubc_14_3).2.2⟩
  · exact ⟨(ubc_14_4).2.1, (ubc_14_4).2.2⟩
  · exact ⟨(ubc_14_5).2.1, (ubc_14_5).2.2⟩
  · exact ⟨(ubc_15_0).2.1, (ubc_15_0).2.2⟩
  · exact ⟨(ubc_15_1).2.1, (ubc_15_1).2.2⟩
  · exact ⟨(ubc_15_2).2.1, (ubc_15_2).2.2⟩
  · exact ⟨(ubc_15_3).2.1, (ubc_15_3).2.2⟩
  · exact ⟨(ubc_15_4).2.1, (ubc_15_4).2.2⟩
  · exact ⟨(ubc_15_5).2.1, (ubc_15_5).2.2⟩
  · exact ⟨(ubc_16_0).2.1, (ubc_16_0).2.2⟩
  · exact ⟨(ubc_16_1).2.1, (ubc_16_1).2.2⟩
  · exact ⟨(ubc_16_2).2.1, (ubc_16_2).2.2⟩
  · exact ⟨(ubc_16_3).2.1, (ubc_16_3).2.2⟩
  · exact ⟨(ubc_16_4).2.1, (ubc_16_4).2.2⟩
  · exact ⟨(ubc_16_5).2.1, (ubc_16_5).2.2⟩
theorem hchkA : ∀ a0 < x2Mult 1 6, ∀ a1 < x2Mult 1 7, ibBatchOK 256 (x2Mult 1 6 * x2Mult 1 7 * x2Mult 1 7) 302 (x2Mult 1 7) (x2Mult 1 6 * x2Mult 1 7) 0 (x2Mult 1 7) ((a0 * x2Mult 1 7 + a1) * x2Mult 1 7) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 17, ∀ a1 < 6, ibBatchOK 256 612 302 6 102 0 6 ((a0 * 6 + a1) * 6) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact (ubc_0_0).1
  · exact (ubc_0_1).1
  · exact (ubc_0_2).1
  · exact (ubc_0_3).1
  · exact (ubc_0_4).1
  · exact (ubc_0_5).1
  · exact (ubc_1_0).1
  · exact (ubc_1_1).1
  · exact (ubc_1_2).1
  · exact (ubc_1_3).1
  · exact (ubc_1_4).1
  · exact (ubc_1_5).1
  · exact (ubc_2_0).1
  · exact (ubc_2_1).1
  · exact (ubc_2_2).1
  · exact (ubc_2_3).1
  · exact (ubc_2_4).1
  · exact (ubc_2_5).1
  · exact (ubc_3_0).1
  · exact (ubc_3_1).1
  · exact (ubc_3_2).1
  · exact (ubc_3_3).1
  · exact (ubc_3_4).1
  · exact (ubc_3_5).1
  · exact (ubc_4_0).1
  · exact (ubc_4_1).1
  · exact (ubc_4_2).1
  · exact (ubc_4_3).1
  · exact (ubc_4_4).1
  · exact (ubc_4_5).1
  · exact (ubc_5_0).1
  · exact (ubc_5_1).1
  · exact (ubc_5_2).1
  · exact (ubc_5_3).1
  · exact (ubc_5_4).1
  · exact (ubc_5_5).1
  · exact (ubc_6_0).1
  · exact (ubc_6_1).1
  · exact (ubc_6_2).1
  · exact (ubc_6_3).1
  · exact (ubc_6_4).1
  · exact (ubc_6_5).1
  · exact (ubc_7_0).1
  · exact (ubc_7_1).1
  · exact (ubc_7_2).1
  · exact (ubc_7_3).1
  · exact (ubc_7_4).1
  · exact (ubc_7_5).1
  · exact (ubc_8_0).1
  · exact (ubc_8_1).1
  · exact (ubc_8_2).1
  · exact (ubc_8_3).1
  · exact (ubc_8_4).1
  · exact (ubc_8_5).1
  · exact (ubc_9_0).1
  · exact (ubc_9_1).1
  · exact (ubc_9_2).1
  · exact (ubc_9_3).1
  · exact (ubc_9_4).1
  · exact (ubc_9_5).1
  · exact (ubc_10_0).1
  · exact (ubc_10_1).1
  · exact (ubc_10_2).1
  · exact (ubc_10_3).1
  · exact (ubc_10_4).1
  · exact (ubc_10_5).1
  · exact (ubc_11_0).1
  · exact (ubc_11_1).1
  · exact (ubc_11_2).1
  · exact (ubc_11_3).1
  · exact (ubc_11_4).1
  · exact (ubc_11_5).1
  · exact (ubc_12_0).1
  · exact (ubc_12_1).1
  · exact (ubc_12_2).1
  · exact (ubc_12_3).1
  · exact (ubc_12_4).1
  · exact (ubc_12_5).1
  · exact (ubc_13_0).1
  · exact (ubc_13_1).1
  · exact (ubc_13_2).1
  · exact (ubc_13_3).1
  · exact (ubc_13_4).1
  · exact (ubc_13_5).1
  · exact (ubc_14_0).1
  · exact (ubc_14_1).1
  · exact (ubc_14_2).1
  · exact (ubc_14_3).1
  · exact (ubc_14_4).1
  · exact (ubc_14_5).1
  · exact (ubc_15_0).1
  · exact (ubc_15_1).1
  · exact (ubc_15_2).1
  · exact (ubc_15_3).1
  · exact (ubc_15_4).1
  · exact (ubc_15_5).1
  · exact (ubc_16_0).1
  · exact (ubc_16_1).1
  · exact (ubc_16_2).1
  · exact (ubc_16_3).1
  · exact (ubc_16_4).1
  · exact (ubc_16_5).1
theorem TTar_0 : (List.range 15).all (fun k => tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 7)).getD (0 + k) (0, 0)) (TTa.getD (0 + k) [])) = true := by decide +kernel
theorem TTarows : ∀ i < nA 1 7, tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 7)).getD i (0, 0)) (TTa.getD i []) = true := by
  show ∀ i < 15, tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 7)).getD i (0, 0)) (TTa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 7)).getD i (0, 0)) (TTa.getD i [])) 0 15 TTar_0 i (Nat.zero_le i) (by omega)
theorem TCar_0 : (List.range 136).all (fun k => tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 7)) ((pairsA (x2Mult 1 6)).getD (0 + k) (0, 0)) (TCa.getD (0 + k) [])) = true := by decide +kernel
theorem TCarows : ∀ i < nA 1 6, tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 7)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TCa.getD i []) = true := by
  show ∀ i < 136, tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 7)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TCa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 7)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TCa.getD i [])) 0 136 TCar_0 i (Nat.zero_le i) (by omega)
theorem TTsr_0 : (List.range 15).all (fun k => tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 7)).getD (0 + k) (0, 0)) (TTs.getD (0 + k) [])) = true := by decide +kernel
theorem TTsrows : ∀ i < nA 1 7, tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 7)).getD i (0, 0)) (TTs.getD i []) = true := by
  show ∀ i < 15, tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 7)).getD i (0, 0)) (TTs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 7)).getD i (0, 0)) (TTs.getD i [])) 0 15 TTsr_0 i (Nat.zero_le i) (by omega)
theorem TCsr_0 : (List.range 136).all (fun k => tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 7)) ((pairsA (x2Mult 1 6)).getD (0 + k) (0, 0)) (TCs.getD (0 + k) [])) = true := by decide +kernel
theorem TCsrows : ∀ i < nA 1 6, tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 7)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TCs.getD i []) = true := by
  show ∀ i < 136, tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 7)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TCs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 7)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TCs.getD i [])) 0 136 TCsr_0 i (Nat.zero_le i) (by omega)

theorem specA (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN164 : N k164 = x2TrialForm 1 k164) (hN165 : N k165 = x2TrialForm 1 k165) :
    TTspecAAS 1 N 6 7 7 TTa ∧ TCspecAAS 1 N 6 7 7 TCa ∧ TTspecSAA 1 N 6 7 7 TTs ∧ TCspecASA 1 N 6 7 7 TCs :=
  tripleSpecA 1 (by decide) N hN 6 7 7 (by decide) (by decide) ks hks hnd (keys N hN164 hN165) hlen UBTa shapeA hchkA TTa TCa TTs TCs
    (tTab_of_rowsG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) (pairsA (x2Mult 1 7)) (nA 1 6) (nA 1 7) (pairsAOK_mult 1 (by decide) 6).1 TTa TTarows)
    (tTabC_of_rowsG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) (pairsA (x2Mult 1 7)) (nA 1 6) (nA 1 7) (pairsAOK_mult 1 (by decide) 7).1 TCa TCarows)
    (tTab_of_rowsG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 6)) (pairsA (x2Mult 1 7)) (nS 1 6) (nA 1 7) (pairsOK_mult 1 (by decide) 6).1 TTs TTsrows)
    (tTabC_of_rowsG UBTa (nS 1 7) 6 2 6 2 (pairsA (x2Mult 1 6)) (pairsU (x2Mult 1 7)) (nA 1 6) (nS 1 7) (pairsOK_mult 1 (by decide) 7).1 TCs TCsrows)

end ThreeCopyQutritWerner.X2.InK1x677
