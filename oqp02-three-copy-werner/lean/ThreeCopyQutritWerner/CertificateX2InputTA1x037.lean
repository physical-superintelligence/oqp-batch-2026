module

public import ThreeCopyQutritWerner.CertificateX2InputU1x037x0
public import ThreeCopyQutritWerner.CertificateX2InputSegA

@[expose] public section


/-! A-pipeline T-tables of the type triple (0, 3, 7) of sector 1 (AAS rows by the second / first A label, SAA, ASA) and their specification. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x037
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBTa ub 1 9
x2_tt_genG TTa UBTa 1 9 6 0 1 1 6 2 2 6
x2_tt_genG TCa UBTa 1 9 6 1 1 1 6 2 2 6
x2_tt_genG TTs UBTa 1 9 6 0 0 1 6 6 2 2
x2_tt_genG TCs UBTa 1 9 6 1 1 0 6 2 6 2

theorem shapeA : ∀ a0 < x2Mult 1 0, ∀ a1 < x2Mult 1 3, ((UBTa.getD a0 []).getD a1 []).length = x2Mult 1 0 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = x2Mult 1 3 := by
  show ∀ a0 < 1, ∀ a1 < 9, ((UBTa.getD a0 []).getD a1 []).length = 1 ∧ ∀ l ∈ (UBTa.getD a0 []).getD a1 [], l.length = 9
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
theorem hchkA : ∀ a0 < x2Mult 1 0, ∀ a1 < x2Mult 1 3, ibBatchOK 256 (x2Mult 1 0 * x2Mult 1 3 * x2Mult 1 7) 302 (x2Mult 1 7) (x2Mult 1 0 * x2Mult 1 3) 0 (x2Mult 1 7) ((a0 * x2Mult 1 3 + a1) * x2Mult 1 7) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 1, ∀ a1 < 9, ibBatchOK 256 54 302 6 9 0 6 ((a0 * 9 + a1) * 6) (ks.flatMap Prod.snd) ((UBTa.getD a0 []).getD a1 []).flatten = true
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
theorem TTar_0 : (List.range 36).all (fun k => tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 0)) ((pairsA (x2Mult 1 3)).getD (0 + k) (0, 0)) (TTa.getD (0 + k) [])) = true := by decide +kernel
theorem TTarows : ∀ i < nA 1 3, tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 0)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TTa.getD i []) = true := by
  show ∀ i < 36, tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 0)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TTa.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 0)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TTa.getD i [])) 0 36 TTar_0 i (Nat.zero_le i) (by omega)
theorem TCarows : ∀ i < nA 1 0, tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 0)).getD i (0, 0)) (TCa.getD i []) = true := by
  show ∀ i < 0, tRowOKG' UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 3)) ((pairsA (x2Mult 1 0)).getD i (0, 0)) (TCa.getD i []) = true
  intro i hi
  exact absurd hi (Nat.not_lt_zero _)
theorem TTsr_0 : (List.range 36).all (fun k => tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 0)) ((pairsA (x2Mult 1 3)).getD (0 + k) (0, 0)) (TTs.getD (0 + k) [])) = true := by decide +kernel
theorem TTsrows : ∀ i < nA 1 3, tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 0)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TTs.getD i []) = true := by
  show ∀ i < 36, tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 0)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TTs.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOKG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 0)) ((pairsA (x2Mult 1 3)).getD i (0, 0)) (TTs.getD i [])) 0 36 TTsr_0 i (Nat.zero_le i) (by omega)
theorem TCsrows : ∀ i < nA 1 0, tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 0)).getD i (0, 0)) (TCs.getD i []) = true := by
  show ∀ i < 0, tRowOKG' UBTa (nS 1 7) 6 2 6 2 (pairsU (x2Mult 1 3)) ((pairsA (x2Mult 1 0)).getD i (0, 0)) (TCs.getD i []) = true
  intro i hi
  exact absurd hi (Nat.not_lt_zero _)

theorem specA (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN21 : N k21 = x2TrialForm 1 k21) :
    TTspecAAS 1 N 0 3 7 TTa ∧ TCspecAAS 1 N 0 3 7 TCa ∧ TTspecSAA 1 N 0 3 7 TTs ∧ TCspecASA 1 N 0 3 7 TCs :=
  tripleSpecA 1 (by decide) N hN 0 3 7 (by decide) (by decide) ks hks hnd (keys N hN21) hlen UBTa shapeA hchkA TTa TCa TTs TCs
    (tTab_of_rowsG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 0)) (pairsA (x2Mult 1 3)) (nA 1 0) (nA 1 3) (pairsAOK_mult 1 (by decide) 0).1 TTa TTarows)
    (tTabC_of_rowsG UBTa (nS 1 7) 6 2 2 6 (pairsA (x2Mult 1 0)) (pairsA (x2Mult 1 3)) (nA 1 0) (nA 1 3) (pairsAOK_mult 1 (by decide) 3).1 TCa TCarows)
    (tTab_of_rowsG UBTa (nS 1 7) 6 6 2 2 (pairsU (x2Mult 1 0)) (pairsA (x2Mult 1 3)) (nS 1 0) (nA 1 3) (pairsOK_mult 1 (by decide) 0).1 TTs TTsrows)
    (tTabC_of_rowsG UBTa (nS 1 7) 6 2 6 2 (pairsA (x2Mult 1 0)) (pairsU (x2Mult 1 3)) (nA 1 0) (nS 1 3) (pairsOK_mult 1 (by decide) 3).1 TCs TCsrows)

end ThreeCopyQutritWerner.X2.InK1x037
