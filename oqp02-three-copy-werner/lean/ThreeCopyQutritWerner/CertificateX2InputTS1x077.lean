module

public import ThreeCopyQutritWerner.CertificateX2InputU1x077x0

@[expose] public section


/-! S-pipeline T-tables of the type triple (0, 7, 7) of sector 1 and their specification (sigma * x2EmbedS at every label triple). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x077
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_ub_table UBT ub 1 6
x2_tt_gen TT UBT 1 6 6 0
x2_tt_gen TC UBT 1 6 6 1

theorem shape : ∀ a0 < x2Mult 1 0, ∀ a1 < x2Mult 1 7, ((UBT.getD a0 []).getD a1 []).length = x2Mult 1 0 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult 1 7 := by
  show ∀ a0 < 1, ∀ a1 < 6, ((UBT.getD a0 []).getD a1 []).length = 1 ∧ ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = 6
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact ⟨(ubc_0_0).2.1, (ubc_0_0).2.2⟩
  · exact ⟨(ubc_0_1).2.1, (ubc_0_1).2.2⟩
  · exact ⟨(ubc_0_2).2.1, (ubc_0_2).2.2⟩
  · exact ⟨(ubc_0_3).2.1, (ubc_0_3).2.2⟩
  · exact ⟨(ubc_0_4).2.1, (ubc_0_4).2.2⟩
  · exact ⟨(ubc_0_5).2.1, (ubc_0_5).2.2⟩
theorem hchk : ∀ a0 < x2Mult 1 0, ∀ a1 < x2Mult 1 7, ibBatchOK 256 (x2Mult 1 0 * x2Mult 1 7 * x2Mult 1 7) 302 (x2Mult 1 7) (x2Mult 1 0 * x2Mult 1 7) 0 (x2Mult 1 7) ((a0 * x2Mult 1 7 + a1) * x2Mult 1 7) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true := by
  show ∀ a0 < 1, ∀ a1 < 6, ibBatchOK 256 36 302 6 6 0 6 ((a0 * 6 + a1) * 6) (ks.flatMap Prod.snd) ((UBT.getD a0 []).getD a1 []).flatten = true
  intro a0 h0 a1 h1
  interval_cases a0 <;> interval_cases a1
  · exact (ubc_0_0).1
  · exact (ubc_0_1).1
  · exact (ubc_0_2).1
  · exact (ubc_0_3).1
  · exact (ubc_0_4).1
  · exact (ubc_0_5).1
theorem TTr_0 : (List.range 21).all (fun k => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 0)) ((pairsU (x2Mult 1 7)).getD (0 + k) (0, 0)) (TT.getD (0 + k) [])) = true := by decide +kernel
theorem TTrows : ∀ i < nS 1 7, tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 0)) ((pairsU (x2Mult 1 7)).getD i (0, 0)) (TT.getD i []) = true := by
  show ∀ i < 21, tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 0)) ((pairsU (x2Mult 1 7)).getD i (0, 0)) (TT.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOK UBT (nS 1 7) (pairsU (x2Mult 1 0)) ((pairsU (x2Mult 1 7)).getD i (0, 0)) (TT.getD i [])) 0 21 TTr_0 i (Nat.zero_le i) (by omega)
theorem TCr_0 : (List.range 1).all (fun k => tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 7)) ((pairsU (x2Mult 1 0)).getD (0 + k) (0, 0)) (TC.getD (0 + k) [])) = true := by decide +kernel
theorem TCrows : ∀ i < nS 1 0, tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 7)) ((pairsU (x2Mult 1 0)).getD i (0, 0)) (TC.getD i []) = true := by
  show ∀ i < 1, tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 7)) ((pairsU (x2Mult 1 0)).getD i (0, 0)) (TC.getD i []) = true
  intro i hi
  exact rangeAll_sound (fun i => tRowOK' UBT (nS 1 7) (pairsU (x2Mult 1 7)) ((pairsU (x2Mult 1 0)).getD i (0, 0)) (TC.getD i [])) 0 1 TCr_0 i (Nat.zero_le i) (by omega)

theorem spec (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hN34 : N k34 = x2TrialForm 1 k34) (hN35 : N k35 = x2TrialForm 1 k35) :
    TTspecS 1 N 0 7 7 TT ∧ TCspecS 1 N 0 7 7 TC := by
  have hk := keys N hN34 hN35
  have htt := tripleSpecS 1 (by decide) N hN 0 7 7 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TT.getD i1 []).getD i0 0) (tTT_of_rows 1 (by decide) UBT 0 7 7 TT TTrows)
  have htc := tripleSpecS 1 (by decide) N hN 0 7 7 (by decide) (by decide) ks hks hnd hk hlen UBT shape hchk (fun i0 i1 => (TC.getD i0 []).getD i1 0) (tTC_of_rows 1 (by decide) UBT 0 7 7 TC TCrows)
  exact ⟨htt, htc⟩

end ThreeCopyQutritWerner.X2.InK1x077
