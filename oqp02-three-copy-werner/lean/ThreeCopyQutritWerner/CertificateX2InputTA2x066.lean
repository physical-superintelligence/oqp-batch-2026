module

public import ThreeCopyQutritWerner.CertificateX2InputU2x066x0
public import ThreeCopyQutritWerner.CertificateX2InputSegA

@[expose] public section


/-! A-pipeline T-tables of the type triple (0, 6, 6) of sector 2 (AAS rows by the second / first A label, SAA, ASA) and their specification. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x066
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBTa ub 1 11
x2_tt_genG TTa UBTa 1 11 11 0 1 1 6 2 2 6
x2_tt_genG TCa UBTa 1 11 11 1 1 1 6 2 2 6
x2_tt_genG TTs UBTa 1 11 11 0 0 1 6 6 2 2
x2_tt_genG TCs UBTa 1 11 11 1 1 0 6 2 6 2

theorem shapeA : ∀ a0 < x2Mult 2 0, ∀ a1 < x2Mult 2 6, ((UBTa.getD a0 []).getD a1 []).length = x2Mult 2 0 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = x2Mult 2 6 := by
  show ∀ a0 < 1, ∀ a1 < 11, ((UBTa.getD a0 []).getD a1 []).length = 1 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = 11
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
theorem hchkA : ∀ a0 < x2Mult 2 0, ∀ a1 < x2Mult 2 6, ibBatchOK 256 (x2Mult 2 0 * x2Mult 2 6 * x2Mult 2 6) 302 (x2Mult 2 6) (x2Mult 2 0 * x2Mult 2 6) 0 (x2Mult 2 6) ((a0 * x2Mult 2 6 + a1) * x2Mult 2 6) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 1, ∀ a1 < 11, ibBatchOK 256 121 302 11 11 0 11 ((a0 * 11 + a1) * 11) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true
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
theorem TTar_0 : (List.range 55).all (fun k => tRowOKG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 0)) ((pairsA (x2Mult 2 6)).getD (0 + k) (0, 0)) (TTa.getD (0 + k) [])) = true := by decide +kernel
theorem TTarows : ∀ i < nA 2 6, tRowOKG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 0)) ((pairsA (x2Mult 2 6)).getD i (0, 0)) (TTa.getD i []) = true := by
  show ∀ i < 55, tRowOKG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 0)) ((pairsA (x2Mult 2 6)).getD i (0, 0)) (TTa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 0)) ((pairsA (x2Mult 2 6)).getD i (0, 0)) (TTa.getD i [])) 0 55 TTar_0 i (Nat.zero_le i) (by omega)
theorem TCarows : ∀ i < nA 2 0, tRowOKG' UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 6)) ((pairsA (x2Mult 2 0)).getD i (0, 0)) (TCa.getD i []) = true := by
  show ∀ i < 0, tRowOKG' UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 6)) ((pairsA (x2Mult 2 0)).getD i (0, 0)) (TCa.getD i []) = true
  intro i hi
  exact absurd hi (Nat.not_lt_zero _)
theorem TTsr_0 : (List.range 55).all (fun k => tRowOKG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 0)) ((pairsA (x2Mult 2 6)).getD (0 + k) (0, 0)) (TTs.getD (0 + k) [])) = true := by decide +kernel
theorem TTsrows : ∀ i < nA 2 6, tRowOKG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 0)) ((pairsA (x2Mult 2 6)).getD i (0, 0)) (TTs.getD i []) = true := by
  show ∀ i < 55, tRowOKG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 0)) ((pairsA (x2Mult 2 6)).getD i (0, 0)) (TTs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 0)) ((pairsA (x2Mult 2 6)).getD i (0, 0)) (TTs.getD i [])) 0 55 TTsr_0 i (Nat.zero_le i) (by omega)
theorem TCsrows : ∀ i < nA 2 0, tRowOKG' UBTa (nS 2 6) 6 2 6 2 (pairsU (x2Mult 2 6)) ((pairsA (x2Mult 2 0)).getD i (0, 0)) (TCs.getD i []) = true := by
  show ∀ i < 0, tRowOKG' UBTa (nS 2 6) 6 2 6 2 (pairsU (x2Mult 2 6)) ((pairsA (x2Mult 2 0)).getD i (0, 0)) (TCs.getD i []) = true
  intro i hi
  exact absurd hi (Nat.not_lt_zero _)

theorem specA (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN26 : N k26 = x2TrialForm 2 k26) (hN27 : N k27 = x2TrialForm 2 k27) :
    TTspecAAS 2 N 0 6 6 TTa ∧ TCspecAAS 2 N 0 6 6 TCa ∧ TTspecSAA 2 N 0 6 6 TTs ∧ TCspecASA 2 N 0 6 6 TCs :=
  tripleSpecA 2 (by decide) N hN 0 6 6 (by decide) (by decide) ks hks hnd (keys N hN26 hN27) hlen UBTa shapeA hchkA TTa TCa TTs TCs
    (tTab_of_rowsG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 0)) (pairsA (x2Mult 2 6)) (nA 2 0) (nA 2 6) (pairsAOK_mult 2 (by decide) 0).1 TTa TTarows)
    (tTabC_of_rowsG UBTa (nS 2 6) 6 2 2 6 (pairsA (x2Mult 2 0)) (pairsA (x2Mult 2 6)) (nA 2 0) (nA 2 6) (pairsAOK_mult 2 (by decide) 6).1 TCa TCarows)
    (tTab_of_rowsG UBTa (nS 2 6) 6 6 2 2 (pairsU (x2Mult 2 0)) (pairsA (x2Mult 2 6)) (nS 2 0) (nA 2 6) (pairsOK_mult 2 (by decide) 0).1 TTs TTsrows)
    (tTabC_of_rowsG UBTa (nS 2 6) 6 2 6 2 (pairsA (x2Mult 2 0)) (pairsU (x2Mult 2 6)) (nA 2 0) (nS 2 6) (pairsOK_mult 2 (by decide) 6).1 TCs TCsrows)

end ThreeCopyQutritWerner.X2.InK2x066
