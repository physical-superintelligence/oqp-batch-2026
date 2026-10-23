module

public import ThreeCopyQutritWerner.CertificateX2InputU1x167x0
public import ThreeCopyQutritWerner.CertificateX2InputSegA

@[expose] public section


/-! A-pipeline T-tables of the type triple (1, 6, 7) of sector 1 (AAS rows by the second / first A label, SAA, ASA) and their specification. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x167
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBTa ub 2 17
x2_tt_genG TTa UBTa 2 17 6 0 1 1 6 2 2 6
x2_tt_genG TCa UBTa 2 17 6 1 1 1 6 2 2 6
x2_tt_genG TTs UBTa 2 17 6 0 0 1 6 6 2 2
x2_tt_genG TCs UBTa 2 17 6 1 1 0 6 2 6 2

theorem shapeA : ∀ a0 < x2Mult 1 1, ∀ a1 < x2Mult 1 6, ((UBTa.getD a0 []).getD a1 []).length = x2Mult 1 1 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = x2Mult 1 6 := by
  show ∀ a0 < 2, ∀ a1 < 17, ((UBTa.getD a0 []).getD a1 []).length = 2 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = 17
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
theorem hchkA : ∀ a0 < x2Mult 1 1, ∀ a1 < x2Mult 1 6, ibBatchOK 256 (x2Mult 1 1 * x2Mult 1 6 * x2Mult 1 7) 302 (x2Mult 1 7) (x2Mult 1 1 * x2Mult 1 6) 0 (x2Mult 1 7) ((a0 * x2Mult 1 6 + a1) * x2Mult 1 7) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 2, ∀ a1 < 17, ibBatchOK 256 204 302 6 34 0 6 ((a0 * 17 + a1) * 6) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true
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
theorem TTar_0 : (List.range 136).all (fun k => tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 1)) ((pairsA (x2Mult 1 6)).getD (0 + k) (0, 0)) (TTa.getD (0 + k) [])) = true := by decide +kernel
theorem TTarows : ∀ i < nA 1 6, tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 1)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTa.getD i []) = true := by
  show ∀ i < 136, tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 1)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 1)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTa.getD i [])) 0 136 TTar_0 i (Nat.zero_le i) (by omega)
theorem TCar_0 : (List.range 1).all (fun k => tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 1)).getD (0 + k) (0, 0)) (TCa.getD (0 + k) [])) = true := by decide +kernel
theorem TCarows : ∀ i < nA 1 1, tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 1)).getD i (0, 0)) (TCa.getD i []) = true := by
  show ∀ i < 1, tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 1)).getD i (0, 0)) (TCa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 1)).getD i (0, 0)) (TCa.getD i [])) 0 1 TCar_0 i (Nat.zero_le i) (by omega)
theorem TTsr_0 : (List.range 136).all (fun k => tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 1)) ((pairsA (x2Mult 1 6)).getD (0 + k) (0, 0)) (TTs.getD (0 + k) [])) = true := by decide +kernel
theorem TTsrows : ∀ i < nA 1 6, tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 1)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTs.getD i []) = true := by
  show ∀ i < 136, tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 1)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 1)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTs.getD i [])) 0 136 TTsr_0 i (Nat.zero_le i) (by omega)
theorem TCsr_0 : (List.range 1).all (fun k => tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 1)).getD (0 + k) (0, 0)) (TCs.getD (0 + k) [])) = true := by decide +kernel
theorem TCsrows : ∀ i < nA 1 1, tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 1)).getD i (0, 0)) (TCs.getD i []) = true := by
  show ∀ i < 1, tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 1)).getD i (0, 0)) (TCs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 1)).getD i (0, 0)) (TCs.getD i [])) 0 1 TCsr_0 i (Nat.zero_le i) (by omega)

theorem specA (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN71 : N k71 = x2TrialForm 1 k71) :
    TTspecAAS 1 N 1 6 7 TTa ∧ TCspecAAS 1 N 1 6 7 TCa ∧ TTspecSAA 1 N 1 6 7 TTs ∧ TCspecASA 1 N 1 6 7 TCs :=
  tripleSpecA 1 (by decide) N hN 1 6 7 (by decide) (by decide) ks hks hnd (keys N hN71) hlen UBTa shapeA hchkA TTa TCa TTs TCs
    (tTab_of_rowsG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 1)) (pairsA (x2Mult 1 6)) (nA 1 1) (nA 1 6) (pairsAOK_mult 1 (by decide) 1).1 TTa TTarows)
    (tTabC_of_rowsG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 1)) (pairsA (x2Mult 1 6)) (nA 1 1) (nA 1 6) (pairsAOK_mult 1 (by decide) 6).1 TCa TCarows)
    (tTab_of_rowsG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 1)) (pairsA (x2Mult 1 6)) (nS 1 1) (nA 1 6) (pairsOK_mult 1 (by decide) 1).1 TTs TTsrows)
    (tTabC_of_rowsG UBTa (nS 1 7) 6 2 6 2 (pairsA (x2Mult 1 1)) (pairsU (x2Mult 1 6)) (nA 1 1) (nS 1 6) (pairsOK_mult 1 (by decide) 6).1 TCs TCsrows)

end ThreeCopyQutritWerner.X2.InK1x167
