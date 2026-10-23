module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (5, 6, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x566
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k154 : x2Key 1 := ⟨154, by decide⟩
x2_gj_cols gj276 276 1 5 6 6 256
theorem gjc154_0 : (List.range 50).all (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 276 (0 + d)) (gj276.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc154_50 : (List.range 50).all (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 276 (50 + d)) (gj276.getD (50 + d) 0)) = true := by decide +kernel
theorem gjc154_100 : (List.range 50).all (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 276 (100 + d)) (gj276.getD (100 + d) 0)) = true := by decide +kernel
theorem gjc154_150 : (List.range 24).all (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 276 (150 + d)) (gj276.getD (150 + d) 0)) = true := by decide +kernel
theorem gjok154 : ∀ d < x2KeySize 1 k154, gjCheck 256 1 (x2KeyTypes 1 k154 0) (x2KeyTypes 1 k154 1) (x2KeyTypes 1 k154 2) (x2KeyMult 1 k154 0) (x2KeyMult 1 k154 1) (x2KeyMult 1 k154 2) (x2JCols (x2KeyGlobal 1 k154) d) (gj276.getD d 0) = true := by
  have hr : x2KeySize 1 k154 = 174 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 5 6 6 7 17 17 (x2JCols 276 d) (gj276.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 50) ∨ (50 ≤ d ∧ d < 100) ∨ (100 ≤ d ∧ d < 150) ∨ (150 ≤ d ∧ d < 174)) with h | h | h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 276 d) (gj276.getD d 0)) 0 50 gjc154_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 276 d) (gj276.getD d 0)) 50 50 gjc154_50 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 276 d) (gj276.getD d 0)) 100 50 gjc154_100 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 276 d) (gj276.getD d 0)) 150 24 gjc154_150 d h.1 (by omega)
x2_v_cols v276 gj276 276 256 2023
theorem vc154_0 : (List.range 22).all (fun c => vCheck 256 2023 174 gj276 (x2Trial_276.getD (0 + c) 0) (v276.getD (0 + c) 0)) = true := by decide +kernel
theorem vc154_22 : (List.range 22).all (fun c => vCheck 256 2023 174 gj276 (x2Trial_276.getD (22 + c) 0) (v276.getD (22 + c) 0)) = true := by decide +kernel
theorem vc154_44 : (List.range 22).all (fun c => vCheck 256 2023 174 gj276 (x2Trial_276.getD (44 + c) 0) (v276.getD (44 + c) 0)) = true := by decide +kernel
theorem vc154_66 : (List.range 22).all (fun c => vCheck 256 2023 174 gj276 (x2Trial_276.getD (66 + c) 0) (v276.getD (66 + c) 0)) = true := by decide +kernel
theorem vc154_88 : (List.range 22).all (fun c => vCheck 256 2023 174 gj276 (x2Trial_276.getD (88 + c) 0) (v276.getD (88 + c) 0)) = true := by decide +kernel
theorem vc154_110 : (List.range 22).all (fun c => vCheck 256 2023 174 gj276 (x2Trial_276.getD (110 + c) 0) (v276.getD (110 + c) 0)) = true := by decide +kernel
theorem vok154 : ∀ c < 132, vCheck 256 (x2KeyMult 1 k154 0 * x2KeyMult 1 k154 1 * x2KeyMult 1 k154 2) (x2KeySize 1 k154) gj276 (x2Trial_276.getD c 0) (v276.getD c 0) = true := by
  intro c hc
  show vCheck 256 2023 174 gj276 (x2Trial_276.getD c 0) (v276.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 22) ∨ (22 ≤ c ∧ c < 44) ∨ (44 ≤ c ∧ c < 66) ∨ (66 ≤ c ∧ c < 88) ∨ (88 ≤ c ∧ c < 110) ∨ (110 ≤ c ∧ c < 132)) with h | h | h | h | h | h
  · exact rangeAll_sound (fun c => vCheck 256 2023 174 gj276 (x2Trial_276.getD c 0) (v276.getD c 0)) 0 22 vc154_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 174 gj276 (x2Trial_276.getD c 0) (v276.getD c 0)) 22 22 vc154_22 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 174 gj276 (x2Trial_276.getD c 0) (v276.getD c 0)) 44 22 vc154_44 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 174 gj276 (x2Trial_276.getD c 0) (v276.getD c 0)) 66 22 vc154_66 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 174 gj276 (x2Trial_276.getD c 0) (v276.getD c 0)) 88 22 vc154_88 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 174 gj276 (x2Trial_276.getD c 0) (v276.getD c 0)) 110 22 vc154_110 c h.1 (by omega)
theorem small154 : x2KeyDegree 1 k154 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k154 0 ∧ 1 ≤ x2KeyMult 1 k154 1 ∧ 1 ≤ x2KeyMult 1 k154 2 ∧ glRowOK 1 (x2KeyTypes 1 k154 0) (x2KeyMult 1 k154 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k154 1) (x2KeyMult 1 k154 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k154 2) (x2KeyMult 1 k154 2) 512 = true ∧ gj276.length = x2KeySize 1 k154 ∧ x2KeySize 1 k154 ≤ 512 ∧ v276.length = 132 := by decide +kernel
theorem chk154 : trialKeyChk 1 k154 132 gj276 x2Trial_276 v276 :=
  trialKeyChk_intro 1 k154 132 gj276 x2Trial_276 v276 small154 gjok154 vok154
def k155 : x2Key 1 := ⟨155, by decide⟩
x2_gj_cols gj277 277 1 5 6 6 256
theorem gjc155_0 : (List.range 50).all (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 277 (0 + d)) (gj277.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc155_50 : (List.range 50).all (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 277 (50 + d)) (gj277.getD (50 + d) 0)) = true := by decide +kernel
theorem gjc155_100 : (List.range 50).all (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 277 (100 + d)) (gj277.getD (100 + d) 0)) = true := by decide +kernel
theorem gjc155_150 : (List.range 13).all (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 277 (150 + d)) (gj277.getD (150 + d) 0)) = true := by decide +kernel
theorem gjok155 : ∀ d < x2KeySize 1 k155, gjCheck 256 1 (x2KeyTypes 1 k155 0) (x2KeyTypes 1 k155 1) (x2KeyTypes 1 k155 2) (x2KeyMult 1 k155 0) (x2KeyMult 1 k155 1) (x2KeyMult 1 k155 2) (x2JCols (x2KeyGlobal 1 k155) d) (gj277.getD d 0) = true := by
  have hr : x2KeySize 1 k155 = 163 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 5 6 6 7 17 17 (x2JCols 277 d) (gj277.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 50) ∨ (50 ≤ d ∧ d < 100) ∨ (100 ≤ d ∧ d < 150) ∨ (150 ≤ d ∧ d < 163)) with h | h | h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 277 d) (gj277.getD d 0)) 0 50 gjc155_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 277 d) (gj277.getD d 0)) 50 50 gjc155_50 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 277 d) (gj277.getD d 0)) 100 50 gjc155_100 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 5 6 6 7 17 17 (x2JCols 277 d) (gj277.getD d 0)) 150 13 gjc155_150 d h.1 (by omega)
x2_v_cols v277 gj277 277 256 2023
theorem vc155_0 : (List.range 23).all (fun c => vCheck 256 2023 163 gj277 (x2Trial_277.getD (0 + c) 0) (v277.getD (0 + c) 0)) = true := by decide +kernel
theorem vc155_23 : (List.range 23).all (fun c => vCheck 256 2023 163 gj277 (x2Trial_277.getD (23 + c) 0) (v277.getD (23 + c) 0)) = true := by decide +kernel
theorem vc155_46 : (List.range 23).all (fun c => vCheck 256 2023 163 gj277 (x2Trial_277.getD (46 + c) 0) (v277.getD (46 + c) 0)) = true := by decide +kernel
theorem vc155_69 : (List.range 23).all (fun c => vCheck 256 2023 163 gj277 (x2Trial_277.getD (69 + c) 0) (v277.getD (69 + c) 0)) = true := by decide +kernel
theorem vc155_92 : (List.range 23).all (fun c => vCheck 256 2023 163 gj277 (x2Trial_277.getD (92 + c) 0) (v277.getD (92 + c) 0)) = true := by decide +kernel
theorem vc155_115 : (List.range 6).all (fun c => vCheck 256 2023 163 gj277 (x2Trial_277.getD (115 + c) 0) (v277.getD (115 + c) 0)) = true := by decide +kernel
theorem vok155 : ∀ c < 121, vCheck 256 (x2KeyMult 1 k155 0 * x2KeyMult 1 k155 1 * x2KeyMult 1 k155 2) (x2KeySize 1 k155) gj277 (x2Trial_277.getD c 0) (v277.getD c 0) = true := by
  intro c hc
  show vCheck 256 2023 163 gj277 (x2Trial_277.getD c 0) (v277.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 23) ∨ (23 ≤ c ∧ c < 46) ∨ (46 ≤ c ∧ c < 69) ∨ (69 ≤ c ∧ c < 92) ∨ (92 ≤ c ∧ c < 115) ∨ (115 ≤ c ∧ c < 121)) with h | h | h | h | h | h
  · exact rangeAll_sound (fun c => vCheck 256 2023 163 gj277 (x2Trial_277.getD c 0) (v277.getD c 0)) 0 23 vc155_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 163 gj277 (x2Trial_277.getD c 0) (v277.getD c 0)) 23 23 vc155_23 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 163 gj277 (x2Trial_277.getD c 0) (v277.getD c 0)) 46 23 vc155_46 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 163 gj277 (x2Trial_277.getD c 0) (v277.getD c 0)) 69 23 vc155_69 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 163 gj277 (x2Trial_277.getD c 0) (v277.getD c 0)) 92 23 vc155_92 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2023 163 gj277 (x2Trial_277.getD c 0) (v277.getD c 0)) 115 6 vc155_115 c h.1 (by omega)
theorem small155 : x2KeyDegree 1 k155 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k155 0 ∧ 1 ≤ x2KeyMult 1 k155 1 ∧ 1 ≤ x2KeyMult 1 k155 2 ∧ glRowOK 1 (x2KeyTypes 1 k155 0) (x2KeyMult 1 k155 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k155 1) (x2KeyMult 1 k155 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k155 2) (x2KeyMult 1 k155 2) 512 = true ∧ gj277.length = x2KeySize 1 k155 ∧ x2KeySize 1 k155 ≤ 512 ∧ v277.length = 121 := by decide +kernel
theorem chk155 : trialKeyChk 1 k155 121 gj277 x2Trial_277 v277 :=
  trialKeyChk_intro 1 k155 121 gj277 x2Trial_277 v277 small155 gjok155 vok155

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k154, ibFS [(v276, v276, 94810963968000)]), (k155, ibFS [(v277, v277, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![5, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN154 : N k154 = x2TrialForm 1 k154) (hN155 : N k155 = x2TrialForm 1 k155) :
    ∀ e ∈ ks, keyOK (x2Mult 1 5 * x2Mult 1 6 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k154 132 _ gj276 x2Trial_276 v276 (by decide) (by rw [hN154]; exact trialForm_eq 1 k154 132 x2Trial_276 (by decide) rfl) chk154
  · exact keyOK_of_trialChk 1 N k155 121 _ gj277 x2Trial_277 v277 (by decide) (by rw [hN155]; exact trialForm_eq 1 k155 121 x2Trial_277 (by decide) rfl) chk155

end ThreeCopyQutritWerner.X2.InK1x566
