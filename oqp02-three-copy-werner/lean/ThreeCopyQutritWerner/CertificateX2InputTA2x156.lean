module

public import ThreeCopyQutritWerner.CertificateX2InputU2x156x0
public import ThreeCopyQutritWerner.CertificateX2InputSegA

@[expose] public section


/-! A-pipeline T-tables of the type triple (1, 5, 6) of sector 2 (AAS rows by the second / first A label, SAA, ASA) and their specification. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x156
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBTa ub 4 10
x2_tt_genG TTa UBTa 4 10 11 0 1 1 6 2 2 6
x2_tt_genG TCa UBTa 4 10 11 1 1 1 6 2 2 6
x2_tt_genG TTs UBTa 4 10 11 0 0 1 6 6 2 2
x2_tt_genG TCs UBTa 4 10 11 1 1 0 6 2 6 2

theorem shapeA : ∀ a0 < x2Mult 2 1, ∀ a1 < x2Mult 2 5, ((UBTa.getD a0 []).getD a1 []).length = x2Mult 2 1 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = x2Mult 2 5 := by
  show ∀ a0 < 4, ∀ a1 < 10, ((UBTa.getD a0 []).getD a1 []).length = 4 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = 10
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
theorem hchkA : ∀ a0 < x2Mult 2 1, ∀ a1 < x2Mult 2 5, ibBatchOK 256 (x2Mult 2 1 * x2Mult 2 5 * x2Mult 2 6) 302 (x2Mult 2 6) (x2Mult 2 1 * x2Mult 2 5) 0 (x2Mult 2 6) ((a0 * x2Mult 2 5 + a1) * x2Mult 2 6) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 4, ∀ a1 < 10, ibBatchOK 256 440 302 11 40 0 11 ((a0 * 10 + a1) * 11) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true
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
theorem TTar_0 : (List.range 45).all (fun k => tRowOKG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 1)) ((pairsA (x2Mult 2 5)).getD (0 + k) (0, 0)) (TTa.getD (0 + k) [])) = true := by decide +kernel
theorem TTarows : ∀ i < nA 2 5, tRowOKG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 1)) ((pairsA (x2Mult 2 5)).getD i (0, 0)) (TTa.getD i []) = true := by
  show ∀ i < 45, tRowOKG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 1)) ((pairsA (x2Mult 2 5)).getD i (0, 0)) (TTa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 1)) ((pairsA (x2Mult 2 5)).getD i (0, 0)) (TTa.getD i [])) 0 45 TTar_0 i (Nat.zero_le i) (by omega)
theorem TCar_0 : (List.range 6).all (fun k => tRowOKG' UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 5)) ((pairsA (x2Mult 2 1)).getD (0 + k) (0, 0)) (TCa.getD (0 + k) [])) = true := by decide +kernel
theorem TCarows : ∀ i < nA 2 1, tRowOKG' UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 5)) ((pairsA (x2Mult 2 1)).getD i (0, 0)) (TCa.getD i []) = true := by
  show ∀ i < 6, tRowOKG' UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 5)) ((pairsA (x2Mult 2 1)).getD i (0, 0)) (TCa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 5)) ((pairsA (x2Mult 2 1)).getD i (0, 0)) (TCa.getD i [])) 0 6 TCar_0 i (Nat.zero_le i) (by omega)
theorem TTsr_0 : (List.range 45).all (fun k => tRowOKG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 1)) ((pairsA (x2Mult 2 5)).getD (0 + k) (0, 0)) (TTs.getD (0 + k) [])) = true := by decide +kernel
theorem TTsrows : ∀ i < nA 2 5, tRowOKG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 1)) ((pairsA (x2Mult 2 5)).getD i (0, 0)) (TTs.getD i []) = true := by
  show ∀ i < 45, tRowOKG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 1)) ((pairsA (x2Mult 2 5)).getD i (0, 0)) (TTs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 1)) ((pairsA (x2Mult 2 5)).getD i (0, 0)) (TTs.getD i [])) 0 45 TTsr_0 i (Nat.zero_le i) (by omega)
theorem TCsr_0 : (List.range 6).all (fun k => tRowOKG' UBTa (nS 2 6) 6 2 6 2 (pairsU (x2Mult 2 5)) ((pairsA (x2Mult 2 1)).getD (0 + k) (0, 0)) (TCs.getD (0 + k) [])) = true := by decide +kernel
theorem TCsrows : ∀ i < nA 2 1, tRowOKG' UBTa (nS 2 6) 6 2 6 2 (pairsU (x2Mult 2 5)) ((pairsA (x2Mult 2 1)).getD i (0, 0)) (TCs.getD i []) = true := by
  show ∀ i < 6, tRowOKG' UBTa (nS 2 6) 6 2 6 2 (pairsU (x2Mult 2 5)) ((pairsA (x2Mult 2 1)).getD i (0, 0)) (TCs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 2 6) 6 2 6 2 (pairsU (x2Mult 2 5)) ((pairsA (x2Mult 2 1)).getD i (0, 0)) (TCs.getD i [])) 0 6 TCsr_0 i (Nat.zero_le i) (by omega)

theorem specA (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN57 : N k57 = x2TrialForm 2 k57) :
    TTspecAAS 2 N 1 5 6 TTa ∧ TCspecAAS 2 N 1 5 6 TCa ∧ TTspecSAA 2 N 1 5 6 TTs ∧ TCspecASA 2 N 1 5 6 TCs :=
  tripleSpecA 2 (by decide) N hN 1 5 6 (by decide) (by decide) ks hks hnd (keys N hN57) hlen UBTa shapeA hchkA TTa TCa TTs TCs
    (tTab_of_rowsG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 1)) (pairsA (x2Mult 2 5)) (nA 2 1) (nA 2 5) (pairsAOK_mult 2 (by decide) 1).1 TTa TTarows)
    (tTabC_of_rowsG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 1)) (pairsA (x2Mult 2 5)) (nA 2 1) (nA 2 5) (pairsAOK_mult 2 (by decide) 5).1 TCa TCarows)
    (tTab_of_rowsG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 1)) (pairsA (x2Mult 2 5)) (nS 2 1) (nA 2 5) (pairsOK_mult 2 (by decide) 1).1 TTs TTsrows)
    (tTabC_of_rowsG UBTa (nS 2 6) 6 2 6 2 (pairsA (x2Mult 2 1)) (pairsU (x2Mult 2 5)) (nA 2 1) (nS 2 5) (pairsOK_mult 2 (by decide) 5).1 TCs TCsrows)

end ThreeCopyQutritWerner.X2.InK2x156
