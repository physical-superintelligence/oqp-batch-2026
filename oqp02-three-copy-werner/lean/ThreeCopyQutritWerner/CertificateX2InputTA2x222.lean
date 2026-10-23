module

public import ThreeCopyQutritWerner.CertificateX2InputU2x222x0
public import ThreeCopyQutritWerner.CertificateX2InputSegA

@[expose] public section


/-! A-pipeline T-tables of the type triple (2, 2, 2) of sector 2 (AAS rows by the second / first A label, SAA, ASA) and their specification. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x222
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBTa ub 5 5
x2_tt_genG TTa UBTa 5 5 5 0 1 1 6 2 2 6
x2_tt_genG TCa UBTa 5 5 5 1 1 1 6 2 2 6
x2_tt_genG TTs UBTa 5 5 5 0 0 1 6 6 2 2
x2_tt_genG TCs UBTa 5 5 5 1 1 0 6 2 6 2

theorem shapeA : ∀ a0 < x2Mult 2 2, ∀ a1 < x2Mult 2 2, ((UBTa.getD a0 []).getD a1 []).length = x2Mult 2 2 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = x2Mult 2 2 := by
  show ∀ a0 < 5, ∀ a1 < 5, ((UBTa.getD a0 []).getD a1 []).length = 5 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = 5
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
theorem hchkA : ∀ a0 < x2Mult 2 2, ∀ a1 < x2Mult 2 2, ibBatchOK 256 (x2Mult 2 2 * x2Mult 2 2 * x2Mult 2 2) 302 (x2Mult 2 2) (x2Mult 2 2 * x2Mult 2 2) 0 (x2Mult 2 2) ((a0 * x2Mult 2 2 + a1) * x2Mult 2 2) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 5, ∀ a1 < 5, ibBatchOK 256 125 302 5 25 0 5 ((a0 * 5 + a1) * 5) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true
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
theorem TTar_0 : (List.range 10).all (fun k => tRowOKG UBTa (nS 2 2) 6 2 2 6 (pairsA (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD (0 + k) (0, 0)) (TTa.getD (0 + k) [])) = true := by decide +kernel
theorem TTarows : ∀ i < nA 2 2, tRowOKG UBTa (nS 2 2) 6 2 2 6 (pairsA (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TTa.getD i []) = true := by
  show ∀ i < 10, tRowOKG UBTa (nS 2 2) 6 2 2 6 (pairsA (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TTa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 2 2) 6 2 2 6 (pairsA (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TTa.getD i [])) 0 10 TTar_0 i (Nat.zero_le i) (by omega)
theorem TCar_0 : (List.range 10).all (fun k => tRowOKG' UBTa (nS 2 2) 6 2 2 6 (pairsA (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD (0 + k) (0, 0)) (TCa.getD (0 + k) [])) = true := by decide +kernel
theorem TCarows : ∀ i < nA 2 2, tRowOKG' UBTa (nS 2 2) 6 2 2 6 (pairsA (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TCa.getD i []) = true := by
  show ∀ i < 10, tRowOKG' UBTa (nS 2 2) 6 2 2 6 (pairsA (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TCa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 2 2) 6 2 2 6 (pairsA (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TCa.getD i [])) 0 10 TCar_0 i (Nat.zero_le i) (by omega)
theorem TTsr_0 : (List.range 10).all (fun k => tRowOKG UBTa (nS 2 2) 6 6 2 2 (pairsU (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD (0 + k) (0, 0)) (TTs.getD (0 + k) [])) = true := by decide +kernel
theorem TTsrows : ∀ i < nA 2 2, tRowOKG UBTa (nS 2 2) 6 6 2 2 (pairsU (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TTs.getD i []) = true := by
  show ∀ i < 10, tRowOKG UBTa (nS 2 2) 6 6 2 2 (pairsU (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TTs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 2 2) 6 6 2 2 (pairsU (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TTs.getD i [])) 0 10 TTsr_0 i (Nat.zero_le i) (by omega)
theorem TCsr_0 : (List.range 10).all (fun k => tRowOKG' UBTa (nS 2 2) 6 2 6 2 (pairsU (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD (0 + k) (0, 0)) (TCs.getD (0 + k) [])) = true := by decide +kernel
theorem TCsrows : ∀ i < nA 2 2, tRowOKG' UBTa (nS 2 2) 6 2 6 2 (pairsU (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TCs.getD i []) = true := by
  show ∀ i < 10, tRowOKG' UBTa (nS 2 2) 6 2 6 2 (pairsU (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TCs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 2 2) 6 2 6 2 (pairsU (x2Mult 2 2)) ((pairsA (x2Mult 2 2)).getD i (0, 0)) (TCs.getD i [])) 0 10 TCsr_0 i (Nat.zero_le i) (by omega)

theorem specA (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN60 : N k60 = x2TrialForm 2 k60) (hN61 : N k61 = x2TrialForm 2 k61) :
    TTspecAAS 2 N 2 2 2 TTa ∧ TCspecAAS 2 N 2 2 2 TCa ∧ TTspecSAA 2 N 2 2 2 TTs ∧ TCspecASA 2 N 2 2 2 TCs :=
  tripleSpecA 2 (by decide) N hN 2 2 2 (by decide) (by decide) ks hks hnd (keys N hN60 hN61) hlen UBTa shapeA hchkA TTa TCa TTs TCs
    (tTab_of_rowsG UBTa (nS 2 2) 6 2 2 6 (pairsA (x2Mult 2 2)) (pairsA (x2Mult 2 2)) (nA 2 2) (nA 2 2) (pairsAOK_mult 2 (by decide) 2).1 TTa TTarows)
    (tTabC_of_rowsG UBTa (nS 2 2) 6 2 2 6 (pairsA (x2Mult 2 2)) (pairsA (x2Mult 2 2)) (nA 2 2) (nA 2 2) (pairsAOK_mult 2 (by decide) 2).1 TCa TCarows)
    (tTab_of_rowsG UBTa (nS 2 2) 6 6 2 2 (pairsU (x2Mult 2 2)) (pairsA (x2Mult 2 2)) (nS 2 2) (nA 2 2) (pairsOK_mult 2 (by decide) 2).1 TTs TTsrows)
    (tTabC_of_rowsG UBTa (nS 2 2) 6 2 6 2 (pairsA (x2Mult 2 2)) (pairsU (x2Mult 2 2)) (nA 2 2) (nS 2 2) (pairsOK_mult 2 (by decide) 2).1 TCs TCsrows)

end ThreeCopyQutritWerner.X2.InK2x222
