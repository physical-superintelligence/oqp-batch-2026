module

public import ThreeCopyQutritWerner.CertificateX2InputU2x244x0
public import ThreeCopyQutritWerner.CertificateX2InputSegA

@[expose] public section


/-! A-pipeline T-tables of the type triple (2, 4, 4) of sector 2 (AAS rows by the second / first A label, SAA, ASA) and their specification. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x244
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBTa ub 5 15
x2_tt_genG TTa UBTa 5 15 15 0 1 1 6 2 2 6
x2_tt_genG TCa UBTa 5 15 15 1 1 1 6 2 2 6
x2_tt_genG TTs UBTa 5 15 15 0 0 1 6 6 2 2
x2_tt_genG TCs UBTa 5 15 15 1 1 0 6 2 6 2

theorem shapeA : ∀ a0 < x2Mult 2 2, ∀ a1 < x2Mult 2 4, ((UBTa.getD a0 []).getD a1 []).length = x2Mult 2 2 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = x2Mult 2 4 := by
  show ∀ a0 < 5, ∀ a1 < 15, ((UBTa.getD a0 []).getD a1 []).length = 5 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = 15
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
theorem hchkA : ∀ a0 < x2Mult 2 2, ∀ a1 < x2Mult 2 4, ibBatchOK 256 (x2Mult 2 2 * x2Mult 2 4 * x2Mult 2 4) 302 (x2Mult 2 4) (x2Mult 2 2 * x2Mult 2 4) 0 (x2Mult 2 4) ((a0 * x2Mult 2 4 + a1) * x2Mult 2 4) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 5, ∀ a1 < 15, ibBatchOK 256 1125 302 15 75 0 15 ((a0 * 15 + a1) * 15) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true
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
theorem TTar_0 : (List.range 105).all (fun k => tRowOKG UBTa (nS 2 4) 6 2 2 6 (pairsA (x2Mult 2 2)) ((pairsA (x2Mult 2 4)).getD (0 + k) (0, 0)) (TTa.getD (0 + k) [])) = true := by decide +kernel
theorem TTarows : ∀ i < nA 2 4, tRowOKG UBTa (nS 2 4) 6 2 2 6 (pairsA (x2Mult 2 2)) ((pairsA (x2Mult 2 4)).getD i (0, 0)) (TTa.getD i []) = true := by
  show ∀ i < 105, tRowOKG UBTa (nS 2 4) 6 2 2 6 (pairsA (x2Mult 2 2)) ((pairsA (x2Mult 2 4)).getD i (0, 0)) (TTa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 2 4) 6 2 2 6 (pairsA (x2Mult 2 2)) ((pairsA (x2Mult 2 4)).getD i (0, 0)) (TTa.getD i [])) 0 105 TTar_0 i (Nat.zero_le i) (by omega)
theorem TCar_0 : (List.range 10).all (fun k => tRowOKG' UBTa (nS 2 4) 6 2 2 6 (pairsA (x2Mult 2 4)) ((pairsA (x2Mult 2 2)).getD (0 + k) (0, 0)) (TCa.getD (0 + k) [])) = true := by decide +kernel
theorem TCarows : ∀ i < nA 2 2, tRowOKG' UBTa (nS 2 4) 6 2 2 6 (pairsA (x2Mult 2 4)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TCa.getD i []) = true := by
  show ∀ i < 10, tRowOKG' UBTa (nS 2 4) 6 2 2 6 (pairsA (x2Mult 2 4)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TCa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 2 4) 6 2 2 6 (pairsA (x2Mult 2 4)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TCa.getD i [])) 0 10 TCar_0 i (Nat.zero_le i) (by omega)
theorem TTsr_0 : (List.range 105).all (fun k => tRowOKG UBTa (nS 2 4) 6 6 2 2 (pairsU (x2Mult 2 2)) ((pairsA (x2Mult 2 4)).getD (0 + k) (0, 0)) (TTs.getD (0 + k) [])) = true := by decide +kernel
theorem TTsrows : ∀ i < nA 2 4, tRowOKG UBTa (nS 2 4) 6 6 2 2 (pairsU (x2Mult 2 2)) ((pairsA (x2Mult 2 4)).getD i (0, 0)) (TTs.getD i []) = true := by
  show ∀ i < 105, tRowOKG UBTa (nS 2 4) 6 6 2 2 (pairsU (x2Mult 2 2)) ((pairsA (x2Mult 2 4)).getD i (0, 0)) (TTs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 2 4) 6 6 2 2 (pairsU (x2Mult 2 2)) ((pairsA (x2Mult 2 4)).getD i (0, 0)) (TTs.getD i [])) 0 105 TTsr_0 i (Nat.zero_le i) (by omega)
theorem TCsr_0 : (List.range 10).all (fun k => tRowOKG' UBTa (nS 2 4) 6 2 6 2 (pairsU (x2Mult 2 4)) ((pairsA (x2Mult 2 2)).getD (0 + k) (0, 0)) (TCs.getD (0 + k) [])) = true := by decide +kernel
theorem TCsrows : ∀ i < nA 2 2, tRowOKG' UBTa (nS 2 4) 6 2 6 2 (pairsU (x2Mult 2 4)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TCs.getD i []) = true := by
  show ∀ i < 10, tRowOKG' UBTa (nS 2 4) 6 2 6 2 (pairsU (x2Mult 2 4)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TCs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 2 4) 6 2 6 2 (pairsU (x2Mult 2 4)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TCs.getD i [])) 0 10 TCsr_0 i (Nat.zero_le i) (by omega)

theorem specA (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN75 : N k75 = x2TrialForm 2 k75) (hN76 : N k76 = x2TrialForm 2 k76) :
    TTspecAAS 2 N 2 4 4 TTa ∧ TCspecAAS 2 N 2 4 4 TCa ∧ TTspecSAA 2 N 2 4 4 TTs ∧ TCspecASA 2 N 2 4 4 TCs :=
  tripleSpecA 2 (by decide) N hN 2 4 4 (by decide) (by decide) ks hks hnd (keys N hN75 hN76) hlen UBTa shapeA hchkA TTa TCa TTs TCs
    (tTab_of_rowsG UBTa (nS 2 4) 6 2 2 6 (pairsA (x2Mult 2 2)) (pairsA (x2Mult 2 4)) (nA 2 2) (nA 2 4) (pairsAOK_mult 2 (by decide) 2).1 TTa TTarows)
    (tTabC_of_rowsG UBTa (nS 2 4) 6 2 2 6 (pairsA (x2Mult 2 2)) (pairsA (x2Mult 2 4)) (nA 2 2) (nA 2 4) (pairsAOK_mult 2 (by decide) 4).1 TCa TCarows)
    (tTab_of_rowsG UBTa (nS 2 4) 6 6 2 2 (pairsU (x2Mult 2 2)) (pairsA (x2Mult 2 4)) (nS 2 2) (nA 2 4) (pairsOK_mult 2 (by decide) 2).1 TTs TTsrows)
    (tTabC_of_rowsG UBTa (nS 2 4) 6 2 6 2 (pairsA (x2Mult 2 2)) (pairsU (x2Mult 2 4)) (nA 2 2) (nS 2 4) (pairsOK_mult 2 (by decide) 4).1 TCs TCsrows)

end ThreeCopyQutritWerner.X2.InK2x244
