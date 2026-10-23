module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (6, 6, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x667
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k162 : x2Key 1 := ⟨162, by decide⟩
x2_gj_cols gj284 284 1 6 6 7 256
theorem gjc162_0 : (List.range 58).all (fun d => gjCheck 256 1 6 6 7 17 17 6 (x2JCols 284 (0 + d)) (gj284.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc162_58 : (List.range 58).all (fun d => gjCheck 256 1 6 6 7 17 17 6 (x2JCols 284 (58 + d)) (gj284.getD (58 + d) 0)) = true := by decide +kernel
theorem gjc162_116 : (List.range 37).all (fun d => gjCheck 256 1 6 6 7 17 17 6 (x2JCols 284 (116 + d)) (gj284.getD (116 + d) 0)) = true := by decide +kernel
theorem gjok162 : ∀ d < x2KeySize 1 k162, gjCheck 256 1 (x2KeyTypes 1 k162 0) (x2KeyTypes 1 k162 1) (x2KeyTypes 1 k162 2) (x2KeyMult 1 k162 0) (x2KeyMult 1 k162 1) (x2KeyMult 1 k162 2) (x2JCols (x2KeyGlobal 1 k162) d) (gj284.getD d 0) = true := by
  have hr : x2KeySize 1 k162 = 153 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 6 6 7 17 17 6 (x2JCols 284 d) (gj284.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 58) ∨ (58 ≤ d ∧ d < 116) ∨ (116 ≤ d ∧ d < 153)) with h | h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 7 17 17 6 (x2JCols 284 d) (gj284.getD d 0)) 0 58 gjc162_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 7 17 17 6 (x2JCols 284 d) (gj284.getD d 0)) 58 58 gjc162_58 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 7 17 17 6 (x2JCols 284 d) (gj284.getD d 0)) 116 37 gjc162_116 d h.1 (by omega)
x2_v_cols v284 gj284 284 256 1734
theorem vc162_0 : (List.range 29).all (fun c => vCheck 256 1734 153 gj284 (x2Trial_284.getD (0 + c) 0) (v284.getD (0 + c) 0)) = true := by decide +kernel
theorem vc162_29 : (List.range 29).all (fun c => vCheck 256 1734 153 gj284 (x2Trial_284.getD (29 + c) 0) (v284.getD (29 + c) 0)) = true := by decide +kernel
theorem vc162_58 : (List.range 29).all (fun c => vCheck 256 1734 153 gj284 (x2Trial_284.getD (58 + c) 0) (v284.getD (58 + c) 0)) = true := by decide +kernel
theorem vc162_87 : (List.range 19).all (fun c => vCheck 256 1734 153 gj284 (x2Trial_284.getD (87 + c) 0) (v284.getD (87 + c) 0)) = true := by decide +kernel
theorem vok162 : ∀ c < 106, vCheck 256 (x2KeyMult 1 k162 0 * x2KeyMult 1 k162 1 * x2KeyMult 1 k162 2) (x2KeySize 1 k162) gj284 (x2Trial_284.getD c 0) (v284.getD c 0) = true := by
  intro c hc
  show vCheck 256 1734 153 gj284 (x2Trial_284.getD c 0) (v284.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 29) ∨ (29 ≤ c ∧ c < 58) ∨ (58 ≤ c ∧ c < 87) ∨ (87 ≤ c ∧ c < 106)) with h | h | h | h
  · exact rangeAll_sound (fun c => vCheck 256 1734 153 gj284 (x2Trial_284.getD c 0) (v284.getD c 0)) 0 29 vc162_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 1734 153 gj284 (x2Trial_284.getD c 0) (v284.getD c 0)) 29 29 vc162_29 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 1734 153 gj284 (x2Trial_284.getD c 0) (v284.getD c 0)) 58 29 vc162_58 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 1734 153 gj284 (x2Trial_284.getD c 0) (v284.getD c 0)) 87 19 vc162_87 c h.1 (by omega)
theorem small162 : x2KeyDegree 1 k162 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k162 0 ∧ 1 ≤ x2KeyMult 1 k162 1 ∧ 1 ≤ x2KeyMult 1 k162 2 ∧ glRowOK 1 (x2KeyTypes 1 k162 0) (x2KeyMult 1 k162 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k162 1) (x2KeyMult 1 k162 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k162 2) (x2KeyMult 1 k162 2) 512 = true ∧ gj284.length = x2KeySize 1 k162 ∧ x2KeySize 1 k162 ≤ 512 ∧ v284.length = 106 := by decide +kernel
theorem chk162 : trialKeyChk 1 k162 106 gj284 x2Trial_284 v284 :=
  trialKeyChk_intro 1 k162 106 gj284 x2Trial_284 v284 small162 gjok162 vok162
def k163 : x2Key 1 := ⟨163, by decide⟩
x2_gj_cols gj285 285 1 6 6 7 256
theorem gjc163_0 : (List.range 58).all (fun d => gjCheck 256 1 6 6 7 17 17 6 (x2JCols 285 (0 + d)) (gj285.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc163_58 : (List.range 58).all (fun d => gjCheck 256 1 6 6 7 17 17 6 (x2JCols 285 (58 + d)) (gj285.getD (58 + d) 0)) = true := by decide +kernel
theorem gjc163_116 : (List.range 20).all (fun d => gjCheck 256 1 6 6 7 17 17 6 (x2JCols 285 (116 + d)) (gj285.getD (116 + d) 0)) = true := by decide +kernel
theorem gjok163 : ∀ d < x2KeySize 1 k163, gjCheck 256 1 (x2KeyTypes 1 k163 0) (x2KeyTypes 1 k163 1) (x2KeyTypes 1 k163 2) (x2KeyMult 1 k163 0) (x2KeyMult 1 k163 1) (x2KeyMult 1 k163 2) (x2JCols (x2KeyGlobal 1 k163) d) (gj285.getD d 0) = true := by
  have hr : x2KeySize 1 k163 = 136 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 6 6 7 17 17 6 (x2JCols 285 d) (gj285.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 58) ∨ (58 ≤ d ∧ d < 116) ∨ (116 ≤ d ∧ d < 136)) with h | h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 7 17 17 6 (x2JCols 285 d) (gj285.getD d 0)) 0 58 gjc163_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 7 17 17 6 (x2JCols 285 d) (gj285.getD d 0)) 58 58 gjc163_58 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 6 6 7 17 17 6 (x2JCols 285 d) (gj285.getD d 0)) 116 20 gjc163_116 d h.1 (by omega)
x2_v_cols v285 gj285 285 256 1734
theorem vc163_0 : (List.range 33).all (fun c => vCheck 256 1734 136 gj285 (x2Trial_285.getD (0 + c) 0) (v285.getD (0 + c) 0)) = true := by decide +kernel
theorem vc163_33 : (List.range 33).all (fun c => vCheck 256 1734 136 gj285 (x2Trial_285.getD (33 + c) 0) (v285.getD (33 + c) 0)) = true := by decide +kernel
theorem vc163_66 : (List.range 33).all (fun c => vCheck 256 1734 136 gj285 (x2Trial_285.getD (66 + c) 0) (v285.getD (66 + c) 0)) = true := by decide +kernel
theorem vc163_99 : (List.range 4).all (fun c => vCheck 256 1734 136 gj285 (x2Trial_285.getD (99 + c) 0) (v285.getD (99 + c) 0)) = true := by decide +kernel
theorem vok163 : ∀ c < 103, vCheck 256 (x2KeyMult 1 k163 0 * x2KeyMult 1 k163 1 * x2KeyMult 1 k163 2) (x2KeySize 1 k163) gj285 (x2Trial_285.getD c 0) (v285.getD c 0) = true := by
  intro c hc
  show vCheck 256 1734 136 gj285 (x2Trial_285.getD c 0) (v285.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 33) ∨ (33 ≤ c ∧ c < 66) ∨ (66 ≤ c ∧ c < 99) ∨ (99 ≤ c ∧ c < 103)) with h | h | h | h
  · exact rangeAll_sound (fun c => vCheck 256 1734 136 gj285 (x2Trial_285.getD c 0) (v285.getD c 0)) 0 33 vc163_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 1734 136 gj285 (x2Trial_285.getD c 0) (v285.getD c 0)) 33 33 vc163_33 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 1734 136 gj285 (x2Trial_285.getD c 0) (v285.getD c 0)) 66 33 vc163_66 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 1734 136 gj285 (x2Trial_285.getD c 0) (v285.getD c 0)) 99 4 vc163_99 c h.1 (by omega)
theorem small163 : x2KeyDegree 1 k163 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k163 0 ∧ 1 ≤ x2KeyMult 1 k163 1 ∧ 1 ≤ x2KeyMult 1 k163 2 ∧ glRowOK 1 (x2KeyTypes 1 k163 0) (x2KeyMult 1 k163 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k163 1) (x2KeyMult 1 k163 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k163 2) (x2KeyMult 1 k163 2) 512 = true ∧ gj285.length = x2KeySize 1 k163 ∧ x2KeySize 1 k163 ≤ 512 ∧ v285.length = 103 := by decide +kernel
theorem chk163 : trialKeyChk 1 k163 103 gj285 x2Trial_285 v285 :=
  trialKeyChk_intro 1 k163 103 gj285 x2Trial_285 v285 small163 gjok163 vok163

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k162, ibFS [(v284, v284, 94810963968000)]), (k163, ibFS [(v285, v285, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![6, 6, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN162 : N k162 = x2TrialForm 1 k162) (hN163 : N k163 = x2TrialForm 1 k163) :
    ∀ e ∈ ks, keyOK (x2Mult 1 6 * x2Mult 1 6 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k162 106 _ gj284 x2Trial_284 v284 (by decide) (by rw [hN162]; exact trialForm_eq 1 k162 106 x2Trial_284 (by decide) rfl) chk162
  · exact keyOK_of_trialChk 1 N k163 103 _ gj285 x2Trial_285 v285 (by decide) (by rw [hN163]; exact trialForm_eq 1 k163 103 x2Trial_285 (by decide) rfl) chk163

end ThreeCopyQutritWerner.X2.InK1x667
