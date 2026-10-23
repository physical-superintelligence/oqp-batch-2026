module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 3, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x336
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k90 : x2Key 2 := ⟨90, by decide⟩
x2_gj_cols gj381 381 2 3 3 6 256
theorem gjc90_0 : (List.range 13).all (fun d => gjCheck 256 2 3 3 6 5 5 11 (x2JCols 381 (0 + d)) (gj381.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok90 : ∀ d < x2KeySize 2 k90, gjCheck 256 2 (x2KeyTypes 2 k90 0) (x2KeyTypes 2 k90 1) (x2KeyTypes 2 k90 2) (x2KeyMult 2 k90 0) (x2KeyMult 2 k90 1) (x2KeyMult 2 k90 2) (x2JCols (x2KeyGlobal 2 k90) d) (gj381.getD d 0) = true := by
  have hr : x2KeySize 2 k90 = 13 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 3 6 5 5 11 (x2JCols 381 d) (gj381.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 3 6 5 5 11 (x2JCols 381 d) (gj381.getD d 0)) 0 13 gjc90_0 d (Nat.zero_le d) (by omega)
x2_v_cols v381 gj381 381 256 275
theorem vc90_0 : (List.range 11).all (fun c => vCheck 256 275 13 gj381 (x2Trial_381.getD (0 + c) 0) (v381.getD (0 + c) 0)) = true := by decide +kernel
theorem vok90 : ∀ c < 11, vCheck 256 (x2KeyMult 2 k90 0 * x2KeyMult 2 k90 1 * x2KeyMult 2 k90 2) (x2KeySize 2 k90) gj381 (x2Trial_381.getD c 0) (v381.getD c 0) = true := by
  intro c hc
  show vCheck 256 275 13 gj381 (x2Trial_381.getD c 0) (v381.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 275 13 gj381 (x2Trial_381.getD c 0) (v381.getD c 0)) 0 11 vc90_0 c (Nat.zero_le c) (by omega)
theorem small90 : x2KeyDegree 2 k90 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k90 0 ∧ 1 ≤ x2KeyMult 2 k90 1 ∧ 1 ≤ x2KeyMult 2 k90 2 ∧ glRowOK 2 (x2KeyTypes 2 k90 0) (x2KeyMult 2 k90 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k90 1) (x2KeyMult 2 k90 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k90 2) (x2KeyMult 2 k90 2) 512 = true ∧ gj381.length = x2KeySize 2 k90 ∧ x2KeySize 2 k90 ≤ 512 ∧ v381.length = 11 := by decide +kernel
theorem chk90 : trialKeyChk 2 k90 11 gj381 x2Trial_381 v381 :=
  trialKeyChk_intro 2 k90 11 gj381 x2Trial_381 v381 small90 gjok90 vok90
def k91 : x2Key 2 := ⟨91, by decide⟩
x2_gj_cols gj382 382 2 3 3 6 256
theorem gjc91_0 : (List.range 10).all (fun d => gjCheck 256 2 3 3 6 5 5 11 (x2JCols 382 (0 + d)) (gj382.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok91 : ∀ d < x2KeySize 2 k91, gjCheck 256 2 (x2KeyTypes 2 k91 0) (x2KeyTypes 2 k91 1) (x2KeyTypes 2 k91 2) (x2KeyMult 2 k91 0) (x2KeyMult 2 k91 1) (x2KeyMult 2 k91 2) (x2JCols (x2KeyGlobal 2 k91) d) (gj382.getD d 0) = true := by
  have hr : x2KeySize 2 k91 = 10 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 3 6 5 5 11 (x2JCols 382 d) (gj382.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 3 6 5 5 11 (x2JCols 382 d) (gj382.getD d 0)) 0 10 gjc91_0 d (Nat.zero_le d) (by omega)
x2_v_cols v382 gj382 382 256 275
theorem vc91_0 : (List.range 8).all (fun c => vCheck 256 275 10 gj382 (x2Trial_382.getD (0 + c) 0) (v382.getD (0 + c) 0)) = true := by decide +kernel
theorem vok91 : ∀ c < 8, vCheck 256 (x2KeyMult 2 k91 0 * x2KeyMult 2 k91 1 * x2KeyMult 2 k91 2) (x2KeySize 2 k91) gj382 (x2Trial_382.getD c 0) (v382.getD c 0) = true := by
  intro c hc
  show vCheck 256 275 10 gj382 (x2Trial_382.getD c 0) (v382.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 275 10 gj382 (x2Trial_382.getD c 0) (v382.getD c 0)) 0 8 vc91_0 c (Nat.zero_le c) (by omega)
theorem small91 : x2KeyDegree 2 k91 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k91 0 ∧ 1 ≤ x2KeyMult 2 k91 1 ∧ 1 ≤ x2KeyMult 2 k91 2 ∧ glRowOK 2 (x2KeyTypes 2 k91 0) (x2KeyMult 2 k91 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k91 1) (x2KeyMult 2 k91 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k91 2) (x2KeyMult 2 k91 2) 512 = true ∧ gj382.length = x2KeySize 2 k91 ∧ x2KeySize 2 k91 ≤ 512 ∧ v382.length = 8 := by decide +kernel
theorem chk91 : trialKeyChk 2 k91 8 gj382 x2Trial_382 v382 :=
  trialKeyChk_intro 2 k91 8 gj382 x2Trial_382 v382 small91 gjok91 vok91

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k90, ibFS [(v381, v381, 94810963968000)]), (k91, ibFS [(v382, v382, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![3, 3, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN90 : N k90 = x2TrialForm 2 k90) (hN91 : N k91 = x2TrialForm 2 k91) :
    ∀ e ∈ ks, keyOK (x2Mult 2 3 * x2Mult 2 3 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k90 11 _ gj381 x2Trial_381 v381 (by decide) (by rw [hN90]; exact trialForm_eq 2 k90 11 x2Trial_381 (by decide) rfl) chk90
  · exact keyOK_of_trialChk 2 N k91 8 _ gj382 x2Trial_382 v382 (by decide) (by rw [hN91]; exact trialForm_eq 2 k91 8 x2Trial_382 (by decide) rfl) chk91

end ThreeCopyQutritWerner.X2.InK2x336
