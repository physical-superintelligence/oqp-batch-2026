module

public import ThreeCopyQutritWerner.CertificateX2InputU2x116x0

@[expose] public section


/-! S-pipeline T-tables of the type triple (1, 1, 6) of sector 2 and their specification (sigma * x2EmbedS at every label triple). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x116
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBT ub 4 4
x2_tt_gen TT UBT 4 4 11 0

theorem shape : ∀ a0 < x2Mult 2 1, ∀ a1 < x2Mult 2 1, ((UBT.getD a0 []).getD a1 []).length = x2Mult 2 1 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult 2 1 := by
  show ∀ a0 < 4, ∀ a1 < 4, ((UBT.getD a0 []).getD a1 []).length = 4 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = 4
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact ⟨(ubc_0_0).2.1, (ubc_0_0).2.2⟩
  · exact ⟨(ubc_0_1).2.1, (ubc_0_1).2.2⟩
  · exact ⟨(ubc_0_2).2.1, (ubc_0_2).2.2⟩
  · exact ⟨(ubc_0_3).2.1, (ubc_0_3).2.2⟩
  · exact ⟨(ubc_1_0).2.1, (ubc_1_0).2.2⟩
  · exact ⟨(ubc_1_1).2.1, (ubc_1_1).2.2⟩
  · exact ⟨(ubc_1_2).2.1, (ubc_1_2).2.2⟩
  · exact ⟨(ubc_1_3).2.1, (ubc_1_3).2.2⟩
  · exact ⟨(ubc_2_0).2.1, (ubc_2_0).2.2⟩
  · exact ⟨(ubc_2_1).2.1, (ubc_2_1).2.2⟩
  · exact ⟨(ubc_2_2).2.1, (ubc_2_2).2.2⟩
  · exact ⟨(ubc_2_3).2.1, (ubc_2_3).2.2⟩
  · exact ⟨(ubc_3_0).2.1, (ubc_3_0).2.2⟩
  · exact ⟨(ubc_3_1).2.1, (ubc_3_1).2.2⟩
  · exact ⟨(ubc_3_2).2.1, (ubc_3_2).2.2⟩
  · exact ⟨(ubc_3_3).2.1, (ubc_3_3).2.2⟩
theorem hchk : ∀ a0 < x2Mult 2 1, ∀ a1 < x2Mult 2 1, ibBatchOK 256 (x2Mult 2 1 * x2Mult 2 1 * x2Mult 2 6) 302 (x2Mult 2 6) (x2Mult 2 1 * x2Mult 2 1) 0 (x2Mult 2 6) ((a0 * x2Mult 2 1 + a1) * x2Mult 2 6) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 4, ∀ a1 < 4, ibBatchOK 256 176 302 11 16 0 11 ((a0 * 4 + a1) * 11) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact (ubc_0_0).1
  · exact (ubc_0_1).1
  · exact (ubc_0_2).1
  · exact (ubc_0_3).1
  · exact (ubc_1_0).1
  · exact (ubc_1_1).1
  · exact (ubc_1_2).1
  · exact (ubc_1_3).1
  · exact (ubc_2_0).1
  · exact (ubc_2_1).1
  · exact (ubc_2_2).1
  · exact (ubc_2_3).1
  · exact (ubc_3_0).1
  · exact (ubc_3_1).1
  · exact (ubc_3_2).1
  · exact (ubc_3_3).1
theorem TTr_0 : (List.range 10).all (fun k => tRowOK UBT (nS 2 6) (pairsU (x2Mult 2 1)) ((pairsU (x2Mult 2 1)).getD (0 + k) (0, 0)) (TT.getD (0 + k) [])) = true := by decide +kernel
theorem TTrows : ∀ i < nS 2 1, tRowOK UBT (nS 2 6) (pairsU (x2Mult 2 1)) ((pairsU (x2Mult 2 1)).getD i (0, 0)) (TT.getD i []) = true := by
  show ∀ i < 10, tRowOK UBT (nS 2 6) (pairsU (x2Mult 2 1)) ((pairsU (x2Mult 2 1)).getD i (0, 0)) (TT.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOK UBT (nS 2 6) (pairsU (x2Mult 2 1)) ((pairsU (x2Mult 2 1)).getD i (0, 0)) (TT.getD i [])) 0 10 TTr_0 i (Nat.zero_le i) (by omega)

theorem spec (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hN38 : N k38 = x2TrialForm 2 k38) (hN39 : N k39 = x2TrialForm 2 k39) :
    TTspecS 2 N 1 1 6 TT ∧ TCspecS 2 N 1 1 6 TT := by
  have hk := keys N hN38 hN39
  have htt := tripleSpecS 2 (by decide) N hN 1 1 6 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TT.getD i1 []).getD i0 0) (tTT_of_rows 2 (by decide) UBT 1 1 6 TT TTrows)
  exact ⟨htt, tcSpec_of_tt_eq 2 N 1 6 TT htt⟩

end ThreeCopyQutritWerner.X2.InK2x116
