module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 6, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x466
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k142 : x2Key 1 := ⟨142, by decide⟩
x2_gj_cols gj264 264 1 4 6 6 256
theorem gjc142_0 : (List.range 50).all (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 264 (0 + d)) (gj264.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc142_50 : (List.range 50).all (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 264 (50 + d)) (gj264.getD (50 + d) 0)) = true := by decide +kernel
theorem gjc142_100 : (List.range 50).all (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 264 (100 + d)) (gj264.getD (100 + d) 0)) = true := by decide +kernel
theorem gjc142_150 : (List.range 30).all (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 264 (150 + d)) (gj264.getD (150 + d) 0)) = true := by decide +kernel
theorem gjok142 : ∀ d < x2KeySize 1 k142, gjCheck 256 1 (x2KeyTypes 1 k142 0) (x2KeyTypes 1 k142 1) (x2KeyTypes 1 k142 2) (x2KeyMult 1 k142 0) (x2KeyMult 1 k142 1) (x2KeyMult 1 k142 2) (x2JCols (x2KeyGlobal 1 k142) d) (gj264.getD d 0) = true := by
  have hr : x2KeySize 1 k142 = 180 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 6 6 7 17 17 (x2JCols 264 d) (gj264.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 50) ∨ (50 ≤ d ∧ d < 100) ∨ (100 ≤ d ∧ d < 150) ∨ (150 ≤ d ∧ d < 180)) with h | h | h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 264 d) (gj264.getD d 0)) 0 50 gjc142_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 264 d) (gj264.getD d 0)) 50 50 gjc142_50 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 264 d) (gj264.getD d 0)) 100 50 gjc142_100 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 264 d) (gj264.getD d 0)) 150 30 gjc142_150 d h.1 (by omega)
x2_v_cols v264 gj264 264 256 2023
theorem vc142_0 : (List.range 21).all (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD (0 + c) 0) (v264.getD (0 + c) 0)) = true := by decide +kernel
theorem vc142_21 : (List.range 21).all (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD (21 + c) 0) (v264.getD (21 + c) 0)) = true := by decide +kernel
theorem vc142_42 : (List.range 21).all (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD (42 + c) 0) (v264.getD (42 + c) 0)) = true := by decide +kernel
theorem vc142_63 : (List.range 21).all (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD (63 + c) 0) (v264.getD (63 + c) 0)) = true := by decide +kernel
theorem vc142_84 : (List.range 21).all (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD (84 + c) 0) (v264.getD (84 + c) 0)) = true := by decide +kernel
theorem vc142_105 : (List.range 21).all (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD (105 + c) 0) (v264.getD (105 + c) 0)) = true := by decide +kernel
theorem vc142_126 : (List.range 9).all (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD (126 + c) 0) (v264.getD (126 + c) 0)) = true := by decide +kernel
theorem vok142 : ∀ c < 135, vCheck 256 (x2KeyMult 1 k142 0 * x2KeyMult 1 k142 1 * x2KeyMult 1 k142 2) (x2KeySize 1 k142) gj264 (x2Trial_264.getD c 0) (v264.getD c 0) = true := by
  intro c hc
  show vCheck 256 2023 180 gj264 (x2Trial_264.getD c 0) (v264.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 21) ∨ (21 ≤ c ∧ c < 42) ∨ (42 ≤ c ∧ c < 63) ∨ (63 ≤ c ∧ c < 84) ∨ (84 ≤ c ∧ c < 105) ∨ (105 ≤ c ∧ c < 126) ∨ (126 ≤ c ∧ c < 135)) with h | h | h | h | h | h | h
  · exact rangeAll_sound (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD c 0) (v264.getD c 0)) 0 21 vc142_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD c 0) (v264.getD c 0)) 21 21 vc142_21 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD c 0) (v264.getD c 0)) 42 21 vc142_42 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD c 0) (v264.getD c 0)) 63 21 vc142_63 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD c 0) (v264.getD c 0)) 84 21 vc142_84 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD c 0) (v264.getD c 0)) 105 21 vc142_105 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 180 gj264 (x2Trial_264.getD c 0) (v264.getD c 0)) 126 9 vc142_126 c h.1 (by omega)
theorem small142 : x2KeyDegree 1 k142 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k142 0 ∧ 1 ≤ x2KeyMult 1 k142 1 ∧ 1 ≤ x2KeyMult 1 k142 2 ∧ glRowOK 1 (x2KeyTypes 1 k142 0) (x2KeyMult 1 k142 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k142 1) (x2KeyMult 1 k142 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k142 2) (x2KeyMult 1 k142 2) 512 = true ∧ gj264.length = x2KeySize 1 k142 ∧ x2KeySize 1 k142 ≤ 512 ∧ v264.length = 135 := by decide +kernel
theorem chk142 : trialKeyChk 1 k142 135 gj264 x2Trial_264 v264 :=
  trialKeyChk_intro 1 k142 135 gj264 x2Trial_264 v264 small142 gjok142 vok142
def k143 : x2Key 1 := ⟨143, by decide⟩
x2_gj_cols gj265 265 1 4 6 6 256
theorem gjc143_0 : (List.range 50).all (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 265 (0 + d)) (gj265.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc143_50 : (List.range 50).all (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 265 (50 + d)) (gj265.getD (50 + d) 0)) = true := by decide +kernel
theorem gjc143_100 : (List.range 50).all (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 265 (100 + d)) (gj265.getD (100 + d) 0)) = true := by decide +kernel
theorem gjc143_150 : (List.range 7).all (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 265 (150 + d)) (gj265.getD (150 + d) 0)) = true := by decide +kernel
theorem gjok143 : ∀ d < x2KeySize 1 k143, gjCheck 256 1 (x2KeyTypes 1 k143 0) (x2KeyTypes 1 k143 1) (x2KeyTypes 1 k143 2) (x2KeyMult 1 k143 0) (x2KeyMult 1 k143 1) (x2KeyMult 1 k143 2) (x2JCols (x2KeyGlobal 1 k143) d) (gj265.getD d 0) = true := by
  have hr : x2KeySize 1 k143 = 157 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 6 6 7 17 17 (x2JCols 265 d) (gj265.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 50) ∨ (50 ≤ d ∧ d < 100) ∨ (100 ≤ d ∧ d < 150) ∨ (150 ≤ d ∧ d < 157)) with h | h | h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 265 d) (gj265.getD d 0)) 0 50 gjc143_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 265 d) (gj265.getD d 0)) 50 50 gjc143_50 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 265 d) (gj265.getD d 0)) 100 50 gjc143_100 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 4 6 6 7 17 17 (x2JCols 265 d) (gj265.getD d 0)) 150 7 gjc143_150 d h.1 (by omega)
x2_v_cols v265 gj265 265 256 2023
theorem vc143_0 : (List.range 24).all (fun c => vCheck 256 2023 157 gj265 (x2Trial_265.getD (0 + c) 0) (v265.getD (0 + c) 0)) = true := by decide +kernel
theorem vc143_24 : (List.range 24).all (fun c => vCheck 256 2023 157 gj265 (x2Trial_265.getD (24 + c) 0) (v265.getD (24 + c) 0)) = true := by decide +kernel
theorem vc143_48 : (List.range 24).all (fun c => vCheck 256 2023 157 gj265 (x2Trial_265.getD (48 + c) 0) (v265.getD (48 + c) 0)) = true := by decide +kernel
theorem vc143_72 : (List.range 24).all (fun c => vCheck 256 2023 157 gj265 (x2Trial_265.getD (72 + c) 0) (v265.getD (72 + c) 0)) = true := by decide +kernel
theorem vc143_96 : (List.range 16).all (fun c => vCheck 256 2023 157 gj265 (x2Trial_265.getD (96 + c) 0) (v265.getD (96 + c) 0)) = true := by decide +kernel
theorem vok143 : ∀ c < 112, vCheck 256 (x2KeyMult 1 k143 0 * x2KeyMult 1 k143 1 * x2KeyMult 1 k143 2) (x2KeySize 1 k143) gj265 (x2Trial_265.getD c 0) (v265.getD c 0) = true := by
  intro c hc
  show vCheck 256 2023 157 gj265 (x2Trial_265.getD c 0) (v265.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 24) ∨ (24 ≤ c ∧ c < 48) ∨ (48 ≤ c ∧ c < 72) ∨ (72 ≤ c ∧ c < 96) ∨ (96 ≤ c ∧ c < 112)) with h | h | h | h | h
  · exact rangeAll_sound (fun c => vCheck 256 2023 157 gj265 (x2Trial_265.getD c 0) (v265.getD c 0)) 0 24 vc143_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 157 gj265 (x2Trial_265.getD c 0) (v265.getD c 0)) 24 24 vc143_24 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 157 gj265 (x2Trial_265.getD c 0) (v265.getD c 0)) 48 24 vc143_48 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 157 gj265 (x2Trial_265.getD c 0) (v265.getD c 0)) 72 24 vc143_72 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 157 gj265 (x2Trial_265.getD c 0) (v265.getD c 0)) 96 16 vc143_96 c h.1 (by omega)
theorem small143 : x2KeyDegree 1 k143 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k143 0 ∧ 1 ≤ x2KeyMult 1 k143 1 ∧ 1 ≤ x2KeyMult 1 k143 2 ∧ glRowOK 1 (x2KeyTypes 1 k143 0) (x2KeyMult 1 k143 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k143 1) (x2KeyMult 1 k143 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k143 2) (x2KeyMult 1 k143 2) 512 = true ∧ gj265.length = x2KeySize 1 k143 ∧ x2KeySize 1 k143 ≤ 512 ∧ v265.length = 112 := by decide +kernel
theorem chk143 : trialKeyChk 1 k143 112 gj265 x2Trial_265 v265 :=
  trialKeyChk_intro 1 k143 112 gj265 x2Trial_265 v265 small143 gjok143 vok143

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k142, ibFS [(v264, v264, 94810963968000)]), (k143, ibFS [(v265, v265, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![4, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN142 : N k142 = x2TrialForm 1 k142) (hN143 : N k143 = x2TrialForm 1 k143) :
    ∀ e ∈ ks, keyOK (x2Mult 1 4 * x2Mult 1 6 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k142 135 _ gj264 x2Trial_264 v264 (by decide) (by rw [hN142]; exact trialForm_eq 1 k142 135 x2Trial_264 (by decide) rfl) chk142
  · exact keyOK_of_trialChk 1 N k143 112 _ gj265 x2Trial_265 v265 (by decide) (by rw [hN143]; exact trialForm_eq 1 k143 112 x2Trial_265 (by decide) rfl) chk143

end ThreeCopyQutritWerner.X2.InK1x466
