module

public import ThreeCopyQutritWerner.CertificateX2InputU1x234x0
public import ThreeCopyQutritWerner.CertificateX2InputSegA

@[expose] public section


/-! A-pipeline T-tables of the type triple (2, 3, 4) of sector 1 (AAS rows by the second / first A label, SAA, ASA) and their specification. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x234
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBTa ub 2 9
x2_tt_genG TTa UBTa 2 9 7 0 1 1 6 2 2 6
x2_tt_genG TCa UBTa 2 9 7 1 1 1 6 2 2 6
x2_tt_genG TTs UBTa 2 9 7 0 0 1 6 6 2 2
x2_tt_genG TCs UBTa 2 9 7 1 1 0 6 2 6 2

theorem shapeA : ∀ a0 < x2Mult 1 2, ∀ a1 < x2Mult 1 3, ((UBTa.getD a0 []).getD a1 []).length = x2Mult 1 2 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = x2Mult 1 3 := by
  show ∀ a0 < 2, ∀ a1 < 9, ((UBTa.getD a0 []).getD a1 []).length = 2 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = 9
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
  · exact ⟨(ubc_1_0).2.1, (ubc_1_0).2.2⟩
  · exact ⟨(ubc_1_1).2.1, (ubc_1_1).2.2⟩
  · exact ⟨(ubc_1_2).2.1, (ubc_1_2).2.2⟩
  · exact ⟨(ubc_1_3).2.1, (ubc_1_3).2.2⟩
  · exact ⟨(ubc_1_4).2.1, (ubc_1_4).2.2⟩
  · exact ⟨(ubc_1_5).2.1, (ubc_1_5).2.2⟩
  · exact ⟨(ubc_1_6).2.1, (ubc_1_6).2.2⟩
  · exact ⟨(ubc_1_7).2.1, (ubc_1_7).2.2⟩
  · exact ⟨(ubc_1_8).2.1, (ubc_1_8).2.2⟩
theorem hchkA : ∀ a0 < x2Mult 1 2, ∀ a1 < x2Mult 1 3, ibBatchOK 256 (x2Mult 1 2 * x2Mult 1 3 * x2Mult 1 4) 302 (x2Mult 1 4) (x2Mult 1 2 * x2Mult 1 3) 0 (x2Mult 1 4) ((a0 * x2Mult 1 3 + a1) * x2Mult 1 4) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 2, ∀ a1 < 9, ibBatchOK 256 126 302 7 18 0 7 ((a0 * 9 + a1) * 7) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true
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
  · exact (ubc_1_0).1
  · exact (ubc_1_1).1
  · exact (ubc_1_2).1
  · exact (ubc_1_3).1
  · exact (ubc_1_4).1
  · exact (ubc_1_5).1
  · exact (ubc_1_6).1
  · exact (ubc_1_7).1
  · exact (ubc_1_8).1
theorem TTar_0 : (List.range 36).all (fun k => tRowOKG UBTa (nS 1 4) 6 2 2 6 (pairsA (x2Mult 1 2)) ((pairsA (x2Mult 1 3)).getD (0 + k) (0, 0)) (TTa.getD (0 + k) [])) = true := by decide +kernel
theorem TTarows : ∀ i < nA 1 3, tRowOKG UBTa (nS 1 4) 6 2 2 6 (pairsA (x2Mult 1 2)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TTa.getD i []) = true := by
  show ∀ i < 36, tRowOKG UBTa (nS 1 4) 6 2 2 6 (pairsA (x2Mult 1 2)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TTa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 4) 6 2 2 6 (pairsA (x2Mult 1 2)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TTa.getD i [])) 0 36 TTar_0 i (Nat.zero_le i) (by omega)
theorem TCar_0 : (List.range 1).all (fun k => tRowOKG' UBTa (nS 1 4) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 2)).getD (0 + k) (0, 0)) (TCa.getD (0 + k) [])) = true := by decide +kernel
theorem TCarows : ∀ i < nA 1 2, tRowOKG' UBTa (nS 1 4) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 2)).getD i (0, 0)) (TCa.getD i []) = true := by
  show ∀ i < 1, tRowOKG' UBTa (nS 1 4) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 2)).getD i (0, 0)) (TCa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 1 4) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 2)).getD i (0, 0)) (TCa.getD i [])) 0 1 TCar_0 i (Nat.zero_le i) (by omega)
theorem TTsr_0 : (List.range 36).all (fun k => tRowOKG UBTa (nS 1 4) 6 6 2 2 (pairsU (x2Mult 1 2)) ((pairsA (x2Mult 1 3)).getD (0 + k) (0, 0)) (TTs.getD (0 + k) [])) = true := by decide +kernel
theorem TTsrows : ∀ i < nA 1 3, tRowOKG UBTa (nS 1 4) 6 6 2 2 (pairsU (x2Mult 1 2)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TTs.getD i []) = true := by
  show ∀ i < 36, tRowOKG UBTa (nS 1 4) 6 6 2 2 (pairsU (x2Mult 1 2)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TTs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 4) 6 6 2 2 (pairsU (x2Mult 1 2)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TTs.getD i [])) 0 36 TTsr_0 i (Nat.zero_le i) (by omega)
theorem TCsr_0 : (List.range 1).all (fun k => tRowOKG' UBTa (nS 1 4) 6 2 6 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 2)).getD (0 + k) (0, 0)) (TCs.getD (0 + k) [])) = true := by decide +kernel
theorem TCsrows : ∀ i < nA 1 2, tRowOKG' UBTa (nS 1 4) 6 2 6 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 2)).getD i (0, 0)) (TCs.getD i []) = true := by
  show ∀ i < 1, tRowOKG' UBTa (nS 1 4) 6 2 6 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 2)).getD i (0, 0)) (TCs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 1 4) 6 2 6 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 2)).getD i (0, 0)) (TCs.getD i [])) 0 1 TCsr_0 i (Nat.zero_le i) (by omega)

theorem specA (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN86 : N k86 = x2TrialForm 1 k86) :
    TTspecAAS 1 N 2 3 4 TTa ∧ TCspecAAS 1 N 2 3 4 TCa ∧ TTspecSAA 1 N 2 3 4 TTs ∧ TCspecASA 1 N 2 3 4 TCs :=
  tripleSpecA 1 (by decide) N hN 2 3 4 (by decide) (by decide) ks hks hnd (keys N hN86) hlen UBTa shapeA hchkA TTa TCa TTs TCs
    (tTab_of_rowsG UBTa (nS 1 4) 6 2 2 6 (pairsA (x2Mult 1 2)) (pairsA (x2Mult 1 3)) (nA 1 2) (nA 1 3) (pairsAOK_mult 1 (by decide) 2).1 TTa TTarows)
    (tTabC_of_rowsG UBTa (nS 1 4) 6 2 2 6 (pairsA (x2Mult 1 2)) (pairsA (x2Mult 1 3)) (nA 1 2) (nA 1 3) (pairsAOK_mult 1 (by decide) 3).1 TCa TCarows)
    (tTab_of_rowsG UBTa (nS 1 4) 6 6 2 2 (pairsU (x2Mult 1 2)) (pairsA (x2Mult 1 3)) (nS 1 2) (nA 1 3) (pairsOK_mult 1 (by decide) 2).1 TTs TTsrows)
    (tTabC_of_rowsG UBTa (nS 1 4) 6 2 6 2 (pairsA (x2Mult 1 2)) (pairsU (x2Mult 1 3)) (nA 1 2) (nS 1 3) (pairsOK_mult 1 (by decide) 3).1 TCs TCsrows)

end ThreeCopyQutritWerner.X2.InK1x234
