module

public import ThreeCopyQutritWerner.CertificateX2InputU1x226x0

@[expose] public section


/-! S-pipeline T-tables of the type triple (2, 2, 6) of sector 1 and their specification (sigma * x2EmbedS at every label triple). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x226
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBT ub 2 2
x2_tt_gen TT UBT 2 2 17 0

theorem shape : ∀ a0 < x2Mult 1 2, ∀ a1 < x2Mult 1 2, ((UBT.getD a0 []).getD a1 []).length = x2Mult 1 2 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult 1 2 := by
  show ∀ a0 < 2, ∀ a1 < 2, ((UBT.getD a0 []).getD a1 []).length = 2 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = 2
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact ⟨(ubc_0_0).2.1, (ubc_0_0).2.2⟩
  · exact ⟨(ubc_0_1).2.1, (ubc_0_1).2.2⟩
  · exact ⟨(ubc_1_0).2.1, (ubc_1_0).2.2⟩
  · exact ⟨(ubc_1_1).2.1, (ubc_1_1).2.2⟩
theorem hchk : ∀ a0 < x2Mult 1 2, ∀ a1 < x2Mult 1 2, ibBatchOK 256 (x2Mult 1 2 * x2Mult 1 2 * x2Mult 1 6) 302 (x2Mult 1 6) (x2Mult 1 2 * x2Mult 1 2) 0 (x2Mult 1 6) ((a0 * x2Mult 1 2 + a1) * x2Mult 1 6) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 2, ∀ a1 < 2, ibBatchOK 256 68 302 17 4 0 17 ((a0 * 2 + a1) * 17) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact (ubc_0_0).1
  · exact (ubc_0_1).1
  · exact (ubc_1_0).1
  · exact (ubc_1_1).1
theorem TTr_0 : (List.range 3).all (fun k => tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 2)) ((pairsU (x2Mult 1 2)).getD (0 + k) (0, 0)) (TT.getD (0 + k) [])) = true := by decide +kernel
theorem TTrows : ∀ i < nS 1 2, tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 2)) ((pairsU (x2Mult 1 2)).getD i (0, 0)) (TT.getD i []) = true := by
  show ∀ i < 3, tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 2)) ((pairsU (x2Mult 1 2)).getD i (0, 0)) (TT.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOK UBT (nS 1 6) (pairsU (x2Mult 1 2)) ((pairsU (x2Mult 1 2)).getD i (0, 0)) (TT.getD i [])) 0 3 TTr_0 i (Nat.zero_le i) (by omega)

theorem spec (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN80 : N k80 = x2TrialForm 1 k80) (hN81 : N k81 = x2TrialForm 1 k81) :
    TTspecS 1 N 2 2 6 TT ∧ TCspecS 1 N 2 2 6 TT := by
  have hk := keys N hN80 hN81
  have htt := tripleSpecS 1 (by decide) N hN 2 2 6 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TT.getD i1 []).getD i0 0) (tTT_of_rows 1 (by decide) UBT 2 2 6 TT TTrows)
  exact ⟨htt, tcSpec_of_tt_eq 1 N 2 6 TT htt⟩

end ThreeCopyQutritWerner.X2.InK1x226
