module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 4, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x444
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k101 : x2Key 2 := ⟨101, by decide⟩
x2_gj_cols gj392 392 2 4 4 4 256
theorem gjc101_0 : (List.range 53).all (fun d => gjCheck 256 2 4 4 4 15 15 15 (x2JCols 392 (0 + d)) (gj392.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok101 : ∀ d < x2KeySize 2 k101, gjCheck 256 2 (x2KeyTypes 2 k101 0) (x2KeyTypes 2 k101 1) (x2KeyTypes 2 k101 2) (x2KeyMult 2 k101 0) (x2KeyMult 2 k101 1) (x2KeyMult 2 k101 2) (x2JCols (x2KeyGlobal 2 k101) d) (gj392.getD d 0) = true := by
  have hr : x2KeySize 2 k101 = 53 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 4 4 4 15 15 15 (x2JCols 392 d) (gj392.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 4 4 4 15 15 15 (x2JCols 392 d) (gj392.getD d 0)) 0 53 gjc101_0 d (Nat.zero_le d) (by omega)
x2_v_cols v392 gj392 392 256 3375
theorem vc101_0 : (List.range 49).all (fun c => vCheck 256 3375 53 gj392 (x2Trial_392.getD (0 + c) 0) (v392.getD (0 + c) 0)) = true := by decide +kernel
theorem vok101 : ∀ c < 49, vCheck 256 (x2KeyMult 2 k101 0 * x2KeyMult 2 k101 1 * x2KeyMult 2 k101 2) (x2KeySize 2 k101) gj392 (x2Trial_392.getD c 0) (v392.getD c 0) = true := by
  intro c hc
  show vCheck 256 3375 53 gj392 (x2Trial_392.getD c 0) (v392.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 3375 53 gj392 (x2Trial_392.getD c 0) (v392.getD c 0)) 0 49 vc101_0 c (Nat.zero_le c) (by omega)
theorem small101 : x2KeyDegree 2 k101 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k101 0 ∧ 1 ≤ x2KeyMult 2 k101 1 ∧ 1 ≤ x2KeyMult 2 k101 2 ∧ glRowOK 2 (x2KeyTypes 2 k101 0) (x2KeyMult 2 k101 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k101 1) (x2KeyMult 2 k101 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k101 2) (x2KeyMult 2 k101 2) 512 = true ∧ gj392.length = x2KeySize 2 k101 ∧ x2KeySize 2 k101 ≤ 512 ∧ v392.length = 49 := by decide +kernel
theorem chk101 : trialKeyChk 2 k101 49 gj392 x2Trial_392 v392 :=
  trialKeyChk_intro 2 k101 49 gj392 x2Trial_392 v392 small101 gjok101 vok101
def k102 : x2Key 2 := ⟨102, by decide⟩
x2_gj_cols gj393 393 2 4 4 4 256
theorem gjc102_0 : (List.range 38).all (fun d => gjCheck 256 2 4 4 4 15 15 15 (x2JCols 393 (0 + d)) (gj393.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok102 : ∀ d < x2KeySize 2 k102, gjCheck 256 2 (x2KeyTypes 2 k102 0) (x2KeyTypes 2 k102 1) (x2KeyTypes 2 k102 2) (x2KeyMult 2 k102 0) (x2KeyMult 2 k102 1) (x2KeyMult 2 k102 2) (x2JCols (x2KeyGlobal 2 k102) d) (gj393.getD d 0) = true := by
  have hr : x2KeySize 2 k102 = 38 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 4 4 4 15 15 15 (x2JCols 393 d) (gj393.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 4 4 4 15 15 15 (x2JCols 393 d) (gj393.getD d 0)) 0 38 gjc102_0 d (Nat.zero_le d) (by omega)
x2_v_cols v393 gj393 393 256 3375
theorem vc102_0 : (List.range 34).all (fun c => vCheck 256 3375 38 gj393 (x2Trial_393.getD (0 + c) 0) (v393.getD (0 + c) 0)) = true := by decide +kernel
theorem vok102 : ∀ c < 34, vCheck 256 (x2KeyMult 2 k102 0 * x2KeyMult 2 k102 1 * x2KeyMult 2 k102 2) (x2KeySize 2 k102) gj393 (x2Trial_393.getD c 0) (v393.getD c 0) = true := by
  intro c hc
  show vCheck 256 3375 38 gj393 (x2Trial_393.getD c 0) (v393.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 3375 38 gj393 (x2Trial_393.getD c 0) (v393.getD c 0)) 0 34 vc102_0 c (Nat.zero_le c) (by omega)
theorem small102 : x2KeyDegree 2 k102 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k102 0 ∧ 1 ≤ x2KeyMult 2 k102 1 ∧ 1 ≤ x2KeyMult 2 k102 2 ∧ glRowOK 2 (x2KeyTypes 2 k102 0) (x2KeyMult 2 k102 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k102 1) (x2KeyMult 2 k102 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k102 2) (x2KeyMult 2 k102 2) 512 = true ∧ gj393.length = x2KeySize 2 k102 ∧ x2KeySize 2 k102 ≤ 512 ∧ v393.length = 34 := by decide +kernel
theorem chk102 : trialKeyChk 2 k102 34 gj393 x2Trial_393 v393 :=
  trialKeyChk_intro 2 k102 34 gj393 x2Trial_393 v393 small102 gjok102 vok102
def k103 : x2Key 2 := ⟨103, by decide⟩
x2_gj_cols gj394 394 2 4 4 4 256
theorem gjc103_0 : (List.range 95).all (fun d => gjCheck 256 2 4 4 4 15 15 15 (x2JCols 394 (0 + d)) (gj394.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok103 : ∀ d < x2KeySize 2 k103, gjCheck 256 2 (x2KeyTypes 2 k103 0) (x2KeyTypes 2 k103 1) (x2KeyTypes 2 k103 2) (x2KeyMult 2 k103 0) (x2KeyMult 2 k103 1) (x2KeyMult 2 k103 2) (x2JCols (x2KeyGlobal 2 k103) d) (gj394.getD d 0) = true := by
  have hr : x2KeySize 2 k103 = 95 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 4 4 4 15 15 15 (x2JCols 394 d) (gj394.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 4 4 4 15 15 15 (x2JCols 394 d) (gj394.getD d 0)) 0 95 gjc103_0 d (Nat.zero_le d) (by omega)
x2_v_cols v394 gj394 394 256 3375
theorem vc103_0 : (List.range 86).all (fun c => vCheck 256 3375 95 gj394 (x2Trial_394.getD (0 + c) 0) (v394.getD (0 + c) 0)) = true := by decide +kernel
theorem vok103 : ∀ c < 86, vCheck 256 (x2KeyMult 2 k103 0 * x2KeyMult 2 k103 1 * x2KeyMult 2 k103 2) (x2KeySize 2 k103) gj394 (x2Trial_394.getD c 0) (v394.getD c 0) = true := by
  intro c hc
  show vCheck 256 3375 95 gj394 (x2Trial_394.getD c 0) (v394.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 3375 95 gj394 (x2Trial_394.getD c 0) (v394.getD c 0)) 0 86 vc103_0 c (Nat.zero_le c) (by omega)
x2_p_cols p394 v394 15
theorem pok103 : ∀ c < 86, partnerCheck (x2KeyMult 2 k103 0) (v394.getD c 0) (p394.getD c 0) = true := by
  intro c hc
  show partnerCheck 15 (v394.getD c 0) (p394.getD c 0) = true
  have h : (List.range 86).all (fun c => partnerCheck 15 (v394.getD c 0) (p394.getD c 0)) = true := by
    decide +kernel
  exact List.all_eq_true.mp h c (List.mem_range.mpr hc)
theorem small103 : x2KeyDegree 2 k103 = 2 ∧ x2KeyMult 2 k103 0 = x2KeyMult 2 k103 1 ∧ x2KeyMult 2 k103 1 = x2KeyMult 2 k103 2 ∧ 1 ≤ x2KeyMult 2 k103 0 ∧ glRowOK 2 (x2KeyTypes 2 k103 0) (x2KeyMult 2 k103 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k103 1) (x2KeyMult 2 k103 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k103 2) (x2KeyMult 2 k103 2) 512 = true ∧ gj394.length = x2KeySize 2 k103 ∧ x2KeySize 2 k103 ≤ 512 ∧ v394.length = 86 ∧ p394.length = 86 := by decide +kernel
theorem chk103 : trial2KeyChk 2 k103 86 gj394 x2Trial_394 v394 p394 :=
  trial2KeyChk_intro 2 k103 86 gj394 x2Trial_394 v394 p394 small103 gjok103 vok103 pok103

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k101, ibFS [(v392, v392, 94810963968000)]), (k102, ibFS [(v393, v393, 94810963968000)]), (k103, ibFS [(v394, v394, 94810963968000), (p394, p394, 31603654656000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![4, 4, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN101 : N k101 = x2TrialForm 2 k101) (hN102 : N k102 = x2TrialForm 2 k102) (hN103 : N k103 = x2TrialForm 2 k103) :
    ∀ e ∈ ks, keyOK (x2Mult 2 4 * x2Mult 2 4 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact keyOK_of_trialChk 2 N k101 49 _ gj392 x2Trial_392 v392 (by decide) (by rw [hN101]; exact trialForm_eq 2 k101 49 x2Trial_392 (by decide) rfl) chk101
  · exact keyOK_of_trialChk 2 N k102 34 _ gj393 x2Trial_393 v393 (by decide) (by rw [hN102]; exact trialForm_eq 2 k102 34 x2Trial_393 (by decide) rfl) chk102
  · exact keyOK_of_trial2Chk 2 N k103 86 _ gj394 x2Trial_394 v394 p394 (by decide) (by rw [hN103]; exact trialForm_eq 2 k103 86 x2Trial_394 (by decide) rfl) chk103

end ThreeCopyQutritWerner.X2.InK2x444
