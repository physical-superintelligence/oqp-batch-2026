module

public import ThreeCopyQutritWerner.CertificateX2InputU1x066x0
public import ThreeCopyQutritWerner.CertificateX2InputSegA

@[expose] public section


/-! A-pipeline T-tables of the type triple (0, 6, 6) of sector 1 (AAS rows by the second / first A label, SAA, ASA) and their specification. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x066
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBTa ub 1 17
x2_tt_genG TTa UBTa 1 17 17 0 1 1 6 2 2 6
x2_tt_genG TCa UBTa 1 17 17 1 1 1 6 2 2 6
x2_tt_genG TTs UBTa 1 17 17 0 0 1 6 6 2 2
x2_tt_genG TCs UBTa 1 17 17 1 1 0 6 2 6 2

theorem shapeA : ∀ a0 < x2Mult 1 0, ∀ a1 < x2Mult 1 6, ((UBTa.getD a0 []).getD a1 []).length = x2Mult 1 0 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = x2Mult 1 6 := by
  show ∀ a0 < 1, ∀ a1 < 17, ((UBTa.getD a0 []).getD a1 []).length = 1 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = 17
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
theorem hchkA : ∀ a0 < x2Mult 1 0, ∀ a1 < x2Mult 1 6, ibBatchOK 256 (x2Mult 1 0 * x2Mult 1 6 * x2Mult 1 6) 302 (x2Mult 1 6) (x2Mult 1 0 * x2Mult 1 6) 0 (x2Mult 1 6) ((a0 * x2Mult 1 6 + a1) * x2Mult 1 6) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 1, ∀ a1 < 17, ibBatchOK 256 289 302 17 17 0 17 ((a0 * 17 + a1) * 17) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true
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
theorem TTar_0 : (List.range 136).all (fun k => tRowOKG UBTa (nS 1 6) 6 2 2 6 (pairsA (x2Mult 1 0)) ((pairsA (x2Mult 1 6)).getD (0 + k) (0, 0)) (TTa.getD (0 + k) [])) = true := by decide +kernel
theorem TTarows : ∀ i < nA 1 6, tRowOKG UBTa (nS 1 6) 6 2 2 6 (pairsA (x2Mult 1 0)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTa.getD i []) = true := by
  show ∀ i < 136, tRowOKG UBTa (nS 1 6) 6 2 2 6 (pairsA (x2Mult 1 0)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 6) 6 2 2 6 (pairsA (x2Mult 1 0)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTa.getD i [])) 0 136 TTar_0 i (Nat.zero_le i) (by omega)
theorem TCarows : ∀ i < nA 1 0, tRowOKG' UBTa (nS 1 6) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 0)).getD i (0, 0)) (TCa.getD i []) = true := by
  show ∀ i < 0, tRowOKG' UBTa (nS 1 6) 6 2 2 6 (pairsA (x2Mult 1 6)) ((pairsA (x2Mult 1 0)).getD i (0, 0)) (TCa.getD i []) = true
  intro i hi
  exact absurd hi (Nat.not_lt_zero _)
theorem TTsr_0 : (List.range 136).all (fun k => tRowOKG UBTa (nS 1 6) 6 6 2 2 (pairsU (x2Mult 1 0)) ((pairsA (x2Mult 1 6)).getD (0 + k) (0, 0)) (TTs.getD (0 + k) [])) = true := by decide +kernel
theorem TTsrows : ∀ i < nA 1 6, tRowOKG UBTa (nS 1 6) 6 6 2 2 (pairsU (x2Mult 1 0)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTs.getD i []) = true := by
  show ∀ i < 136, tRowOKG UBTa (nS 1 6) 6 6 2 2 (pairsU (x2Mult 1 0)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 6) 6 6 2 2 (pairsU (x2Mult 1 0)) ((pairsA (x2Mult 1 6)).getD i (0, 0)) (TTs.getD i [])) 0 136 TTsr_0 i (Nat.zero_le i) (by omega)
theorem TCsrows : ∀ i < nA 1 0, tRowOKG' UBTa (nS 1 6) 6 2 6 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 0)).getD i (0, 0)) (TCs.getD i []) = true := by
  show ∀ i < 0, tRowOKG' UBTa (nS 1 6) 6 2 6 2 (pairsU (x2Mult 1 6)) ((pairsA (x2Mult 1 0)).getD i (0, 0)) (TCs.getD i []) = true
  intro i hi
  exact absurd hi (Nat.not_lt_zero _)

theorem specA (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN31 : N k31 = x2TrialForm 1 k31) (hN32 : N k32 = x2TrialForm 1 k32) :
    TTspecAAS 1 N 0 6 6 TTa ∧ TCspecAAS 1 N 0 6 6 TCa ∧ TTspecSAA 1 N 0 6 6 TTs ∧ TCspecASA 1 N 0 6 6 TCs :=
  tripleSpecA 1 (by decide) N hN 0 6 6 (by decide) (by decide) ks hks hnd (keys N hN31 hN32) hlen UBTa shapeA hchkA TTa TCa TTs TCs
    (tTab_of_rowsG UBTa (nS 1 6) 6 2 2 6 (pairsA (x2Mult 1 0)) (pairsA (x2Mult 1 6)) (nA 1 0) (nA 1 6) (pairsAOK_mult 1 (by decide) 0).1 TTa TTarows)
    (tTabC_of_rowsG UBTa (nS 1 6) 6 2 2 6 (pairsA (x2Mult 1 0)) (pairsA (x2Mult 1 6)) (nA 1 0) (nA 1 6) (pairsAOK_mult 1 (by decide) 6).1 TCa TCarows)
    (tTab_of_rowsG UBTa (nS 1 6) 6 6 2 2 (pairsU (x2Mult 1 0)) (pairsA (x2Mult 1 6)) (nS 1 0) (nA 1 6) (pairsOK_mult 1 (by decide) 0).1 TTs TTsrows)
    (tTabC_of_rowsG UBTa (nS 1 6) 6 2 6 2 (pairsA (x2Mult 1 0)) (pairsU (x2Mult 1 6)) (nA 1 0) (nS 1 6) (pairsOK_mult 1 (by decide) 6).1 TCs TCsrows)

end ThreeCopyQutritWerner.X2.InK1x066
