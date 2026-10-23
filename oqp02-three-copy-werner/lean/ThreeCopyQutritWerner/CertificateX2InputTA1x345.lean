module

public import ThreeCopyQutritWerner.CertificateX2InputU1x345x0
public import ThreeCopyQutritWerner.CertificateX2InputSegA

@[expose] public section


/-! A-pipeline T-tables of the type triple (3, 4, 5) of sector 1 (AAS rows by the second / first A label, SAA, ASA) and their specification. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x345
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBTa ub 9 7
x2_tt_genG TTa UBTa 9 7 7 0 1 1 6 2 2 6
x2_tt_genG TCa UBTa 9 7 7 1 1 1 6 2 2 6
x2_tt_genG TTs UBTa 9 7 7 0 0 1 6 6 2 2
x2_tt_genG TCs UBTa 9 7 7 1 1 0 6 2 6 2

theorem shapeA : ∀ a0 < x2Mult 1 3, ∀ a1 < x2Mult 1 4, ((UBTa.getD a0 []).getD a1 []).length = x2Mult 1 3 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = x2Mult 1 4 := by
  show ∀ a0 < 9, ∀ a1 < 7, ((UBTa.getD a0 []).getD a1 []).length = 9 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = 7
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact ⟨(ubc_0_0).2.1, (ubc_0_0).2.2⟩
  · exact ⟨(ubc_0_1).2.1, (ubc_0_1).2.2⟩
  · exact ⟨(ubc_0_2).2.1, (ubc_0_2).2.2⟩
  · exact ⟨(ubc_0_3).2.1, (ubc_0_3).2.2⟩
  · exact ⟨(ubc_0_4).2.1, (ubc_0_4).2.2⟩
  · exact ⟨(ubc_0_5).2.1, (ubc_0_5).2.2⟩
  · exact ⟨(ubc_0_6).2.1, (ubc_0_6).2.2⟩
  · exact ⟨(ubc_1_0).2.1, (ubc_1_0).2.2⟩
  · exact ⟨(ubc_1_1).2.1, (ubc_1_1).2.2⟩
  · exact ⟨(ubc_1_2).2.1, (ubc_1_2).2.2⟩
  · exact ⟨(ubc_1_3).2.1, (ubc_1_3).2.2⟩
  · exact ⟨(ubc_1_4).2.1, (ubc_1_4).2.2⟩
  · exact ⟨(ubc_1_5).2.1, (ubc_1_5).2.2⟩
  · exact ⟨(ubc_1_6).2.1, (ubc_1_6).2.2⟩
  · exact ⟨(ubc_2_0).2.1, (ubc_2_0).2.2⟩
  · exact ⟨(ubc_2_1).2.1, (ubc_2_1).2.2⟩
  · exact ⟨(ubc_2_2).2.1, (ubc_2_2).2.2⟩
  · exact ⟨(ubc_2_3).2.1, (ubc_2_3).2.2⟩
  · exact ⟨(ubc_2_4).2.1, (ubc_2_4).2.2⟩
  · exact ⟨(ubc_2_5).2.1, (ubc_2_5).2.2⟩
  · exact ⟨(ubc_2_6).2.1, (ubc_2_6).2.2⟩
  · exact ⟨(ubc_3_0).2.1, (ubc_3_0).2.2⟩
  · exact ⟨(ubc_3_1).2.1, (ubc_3_1).2.2⟩
  · exact ⟨(ubc_3_2).2.1, (ubc_3_2).2.2⟩
  · exact ⟨(ubc_3_3).2.1, (ubc_3_3).2.2⟩
  · exact ⟨(ubc_3_4).2.1, (ubc_3_4).2.2⟩
  · exact ⟨(ubc_3_5).2.1, (ubc_3_5).2.2⟩
  · exact ⟨(ubc_3_6).2.1, (ubc_3_6).2.2⟩
  · exact ⟨(ubc_4_0).2.1, (ubc_4_0).2.2⟩
  · exact ⟨(ubc_4_1).2.1, (ubc_4_1).2.2⟩
  · exact ⟨(ubc_4_2).2.1, (ubc_4_2).2.2⟩
  · exact ⟨(ubc_4_3).2.1, (ubc_4_3).2.2⟩
  · exact ⟨(ubc_4_4).2.1, (ubc_4_4).2.2⟩
  · exact ⟨(ubc_4_5).2.1, (ubc_4_5).2.2⟩
  · exact ⟨(ubc_4_6).2.1, (ubc_4_6).2.2⟩
  · exact ⟨(ubc_5_0).2.1, (ubc_5_0).2.2⟩
  · exact ⟨(ubc_5_1).2.1, (ubc_5_1).2.2⟩
  · exact ⟨(ubc_5_2).2.1, (ubc_5_2).2.2⟩
  · exact ⟨(ubc_5_3).2.1, (ubc_5_3).2.2⟩
  · exact ⟨(ubc_5_4).2.1, (ubc_5_4).2.2⟩
  · exact ⟨(ubc_5_5).2.1, (ubc_5_5).2.2⟩
  · exact ⟨(ubc_5_6).2.1, (ubc_5_6).2.2⟩
  · exact ⟨(ubc_6_0).2.1, (ubc_6_0).2.2⟩
  · exact ⟨(ubc_6_1).2.1, (ubc_6_1).2.2⟩
  · exact ⟨(ubc_6_2).2.1, (ubc_6_2).2.2⟩
  · exact ⟨(ubc_6_3).2.1, (ubc_6_3).2.2⟩
  · exact ⟨(ubc_6_4).2.1, (ubc_6_4).2.2⟩
  · exact ⟨(ubc_6_5).2.1, (ubc_6_5).2.2⟩
  · exact ⟨(ubc_6_6).2.1, (ubc_6_6).2.2⟩
  · exact ⟨(ubc_7_0).2.1, (ubc_7_0).2.2⟩
  · exact ⟨(ubc_7_1).2.1, (ubc_7_1).2.2⟩
  · exact ⟨(ubc_7_2).2.1, (ubc_7_2).2.2⟩
  · exact ⟨(ubc_7_3).2.1, (ubc_7_3).2.2⟩
  · exact ⟨(ubc_7_4).2.1, (ubc_7_4).2.2⟩
  · exact ⟨(ubc_7_5).2.1, (ubc_7_5).2.2⟩
  · exact ⟨(ubc_7_6).2.1, (ubc_7_6).2.2⟩
  · exact ⟨(ubc_8_0).2.1, (ubc_8_0).2.2⟩
  · exact ⟨(ubc_8_1).2.1, (ubc_8_1).2.2⟩
  · exact ⟨(ubc_8_2).2.1, (ubc_8_2).2.2⟩
  · exact ⟨(ubc_8_3).2.1, (ubc_8_3).2.2⟩
  · exact ⟨(ubc_8_4).2.1, (ubc_8_4).2.2⟩
  · exact ⟨(ubc_8_5).2.1, (ubc_8_5).2.2⟩
  · exact ⟨(ubc_8_6).2.1, (ubc_8_6).2.2⟩
theorem hchkA : ∀ a0 < x2Mult 1 3, ∀ a1 < x2Mult 1 4, ibBatchOK 256 (x2Mult 1 3 * x2Mult 1 4 * x2Mult 1 5) 302 (x2Mult 1 5) (x2Mult 1 3 * x2Mult 1 4) 0 (x2Mult 1 5) ((a0 * x2Mult 1 4 + a1) * x2Mult 1 5) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 9, ∀ a1 < 7, ibBatchOK 256 441 302 7 63 0 7 ((a0 * 7 + a1) * 7) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact (ubc_0_0).1
  · exact (ubc_0_1).1
  · exact (ubc_0_2).1
  · exact (ubc_0_3).1
  · exact (ubc_0_4).1
  · exact (ubc_0_5).1
  · exact (ubc_0_6).1
  · exact (ubc_1_0).1
  · exact (ubc_1_1).1
  · exact (ubc_1_2).1
  · exact (ubc_1_3).1
  · exact (ubc_1_4).1
  · exact (ubc_1_5).1
  · exact (ubc_1_6).1
  · exact (ubc_2_0).1
  · exact (ubc_2_1).1
  · exact (ubc_2_2).1
  · exact (ubc_2_3).1
  · exact (ubc_2_4).1
  · exact (ubc_2_5).1
  · exact (ubc_2_6).1
  · exact (ubc_3_0).1
  · exact (ubc_3_1).1
  · exact (ubc_3_2).1
  · exact (ubc_3_3).1
  · exact (ubc_3_4).1
  · exact (ubc_3_5).1
  · exact (ubc_3_6).1
  · exact (ubc_4_0).1
  · exact (ubc_4_1).1
  · exact (ubc_4_2).1
  · exact (ubc_4_3).1
  · exact (ubc_4_4).1
  · exact (ubc_4_5).1
  · exact (ubc_4_6).1
  · exact (ubc_5_0).1
  · exact (ubc_5_1).1
  · exact (ubc_5_2).1
  · exact (ubc_5_3).1
  · exact (ubc_5_4).1
  · exact (ubc_5_5).1
  · exact (ubc_5_6).1
  · exact (ubc_6_0).1
  · exact (ubc_6_1).1
  · exact (ubc_6_2).1
  · exact (ubc_6_3).1
  · exact (ubc_6_4).1
  · exact (ubc_6_5).1
  · exact (ubc_6_6).1
  · exact (ubc_7_0).1
  · exact (ubc_7_1).1
  · exact (ubc_7_2).1
  · exact (ubc_7_3).1
  · exact (ubc_7_4).1
  · exact (ubc_7_5).1
  · exact (ubc_7_6).1
  · exact (ubc_8_0).1
  · exact (ubc_8_1).1
  · exact (ubc_8_2).1
  · exact (ubc_8_3).1
  · exact (ubc_8_4).1
  · exact (ubc_8_5).1
  · exact (ubc_8_6).1
theorem TTar_0 : (List.range 21).all (fun k => tRowOKG UBTa (nS 1 5) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 4)).getD (0 + k) (0, 0)) (TTa.getD (0 + k) [])) = true := by decide +kernel
theorem TTarows : ∀ i < nA 1 4, tRowOKG UBTa (nS 1 5) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 4)).getD i (0, 0)) (TTa.getD i []) = true := by
  show ∀ i < 21, tRowOKG UBTa (nS 1 5) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 4)).getD i (0, 0)) (TTa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 5) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 4)).getD i (0, 0)) (TTa.getD i [])) 0 21 TTar_0 i (Nat.zero_le i) (by omega)
theorem TCar_0 : (List.range 36).all (fun k => tRowOKG' UBTa (nS 1 5) 6 2 2 6 (pairsA (x2Mult 1 4)) ((pairsA (x2Mult 1 3)).getD (0 + k) (0, 0)) (TCa.getD (0 + k) [])) = true := by decide +kernel
theorem TCarows : ∀ i < nA 1 3, tRowOKG' UBTa (nS 1 5) 6 2 2 6 (pairsA (x2Mult 1 4)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TCa.getD i []) = true := by
  show ∀ i < 36, tRowOKG' UBTa (nS 1 5) 6 2 2 6 (pairsA (x2Mult 1 4)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TCa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 1 5) 6 2 2 6 (pairsA (x2Mult 1 4)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TCa.getD i [])) 0 36 TCar_0 i (Nat.zero_le i) (by omega)
theorem TTsr_0 : (List.range 21).all (fun k => tRowOKG UBTa (nS 1 5) 6 6 2 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 4)).getD (0 + k) (0, 0)) (TTs.getD (0 + k) [])) = true := by decide +kernel
theorem TTsrows : ∀ i < nA 1 4, tRowOKG UBTa (nS 1 5) 6 6 2 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 4)).getD i (0, 0)) (TTs.getD i []) = true := by
  show ∀ i < 21, tRowOKG UBTa (nS 1 5) 6 6 2 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 4)).getD i (0, 0)) (TTs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 5) 6 6 2 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 4)).getD i (0, 0)) (TTs.getD i [])) 0 21 TTsr_0 i (Nat.zero_le i) (by omega)
theorem TCsr_0 : (List.range 36).all (fun k => tRowOKG' UBTa (nS 1 5) 6 2 6 2 (pairsU (x2Mult 1 4)) ((pairsA (x2Mult 1 3)).getD (0 + k) (0, 0)) (TCs.getD (0 + k) [])) = true := by decide +kernel
theorem TCsrows : ∀ i < nA 1 3, tRowOKG' UBTa (nS 1 5) 6 2 6 2 (pairsU (x2Mult 1 4)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TCs.getD i []) = true := by
  show ∀ i < 36, tRowOKG' UBTa (nS 1 5) 6 2 6 2 (pairsU (x2Mult 1 4)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TCs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 1 5) 6 2 6 2 (pairsU (x2Mult 1 4)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TCs.getD i [])) 0 36 TCsr_0 i (Nat.zero_le i) (by omega)

theorem specA (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN117 : N k117 = x2TrialForm 1 k117) :
    TTspecAAS 1 N 3 4 5 TTa ∧ TCspecAAS 1 N 3 4 5 TCa ∧ TTspecSAA 1 N 3 4 5 TTs ∧ TCspecASA 1 N 3 4 5 TCs :=
  tripleSpecA 1 (by decide) N hN 3 4 5 (by decide) (by decide) ks hks hnd (keys N hN117) hlen UBTa shapeA hchkA TTa TCa TTs TCs
    (tTab_of_rowsG UBTa (nS 1 5) 6 2 2 6 (pairsA (x2Mult 1 3)) (pairsA (x2Mult 1 4)) (nA 1 3) (nA 1 4) (pairsAOK_mult 1 (by decide) 3).1 TTa TTarows)
    (tTabC_of_rowsG UBTa (nS 1 5) 6 2 2 6 (pairsA (x2Mult 1 3)) (pairsA (x2Mult 1 4)) (nA 1 3) (nA 1 4) (pairsAOK_mult 1 (by decide) 4).1 TCa TCarows)
    (tTab_of_rowsG UBTa (nS 1 5) 6 6 2 2 (pairsU (x2Mult 1 3)) (pairsA (x2Mult 1 4)) (nS 1 3) (nA 1 4) (pairsOK_mult 1 (by decide) 3).1 TTs TTsrows)
    (tTabC_of_rowsG UBTa (nS 1 5) 6 2 6 2 (pairsA (x2Mult 1 3)) (pairsU (x2Mult 1 4)) (nA 1 3) (nS 1 4) (pairsOK_mult 1 (by decide) 4).1 TCs TCsrows)

end ThreeCopyQutritWerner.X2.InK1x345
