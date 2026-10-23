module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 6, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x366
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k124 : x2Key 1 := ⟨124, by decide⟩
x2_gj_cols gj246 246 1 3 6 6 256
theorem gjc124_0 : (List.range 39).all (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 (0 + d)) (gj246.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc124_39 : (List.range 39).all (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 (39 + d)) (gj246.getD (39 + d) 0)) = true := by decide +kernel
theorem gjc124_78 : (List.range 39).all (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 (78 + d)) (gj246.getD (78 + d) 0)) = true := by decide +kernel
theorem gjc124_117 : (List.range 39).all (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 (117 + d)) (gj246.getD (117 + d) 0)) = true := by decide +kernel
theorem gjc124_156 : (List.range 39).all (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 (156 + d)) (gj246.getD (156 + d) 0)) = true := by decide +kernel
theorem gjc124_195 : (List.range 30).all (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 (195 + d)) (gj246.getD (195 + d) 0)) = true := by decide +kernel
theorem gjok124 : ∀ d < x2KeySize 1 k124, gjCheck 256 1 (x2KeyTypes 1 k124 0) (x2KeyTypes 1 k124 1) (x2KeyTypes 1 k124 2) (x2KeyMult 1 k124 0) (x2KeyMult 1 k124 1) (x2KeyMult 1 k124 2) (x2JCols (x2KeyGlobal 1 k124) d) (gj246.getD d 0) = true := by
  have hr : x2KeySize 1 k124 = 225 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 d) (gj246.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 39) ∨ (39 ≤ d ∧ d < 78) ∨ (78 ≤ d ∧ d < 117) ∨ (117 ≤ d ∧ d < 156) ∨ (156 ≤ d ∧ d < 195) ∨ (195 ≤ d ∧ d < 225)) with h | h | h | h | h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 d) (gj246.getD d 0)) 0 39 gjc124_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 d) (gj246.getD d 0)) 39 39 gjc124_39 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 d) (gj246.getD d 0)) 78 39 gjc124_78 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 d) (gj246.getD d 0)) 117 39 gjc124_117 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 d) (gj246.getD d 0)) 156 39 gjc124_156 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 246 d) (gj246.getD d 0)) 195 30 gjc124_195 d h.1 (by omega)
x2_v_cols v246 gj246 246 256 2601
theorem vc124_0 : (List.range 13).all (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD (0 + c) 0) (v246.getD (0 + c) 0)) = true := by decide +kernel
theorem vc124_13 : (List.range 13).all (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD (13 + c) 0) (v246.getD (13 + c) 0)) = true := by decide +kernel
theorem vc124_26 : (List.range 13).all (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD (26 + c) 0) (v246.getD (26 + c) 0)) = true := by decide +kernel
theorem vc124_39 : (List.range 13).all (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD (39 + c) 0) (v246.getD (39 + c) 0)) = true := by decide +kernel
theorem vc124_52 : (List.range 13).all (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD (52 + c) 0) (v246.getD (52 + c) 0)) = true := by decide +kernel
theorem vc124_65 : (List.range 13).all (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD (65 + c) 0) (v246.getD (65 + c) 0)) = true := by decide +kernel
theorem vc124_78 : (List.range 13).all (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD (78 + c) 0) (v246.getD (78 + c) 0)) = true := by decide +kernel
theorem vc124_91 : (List.range 13).all (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD (91 + c) 0) (v246.getD (91 + c) 0)) = true := by decide +kernel
theorem vc124_104 : (List.range 13).all (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD (104 + c) 0) (v246.getD (104 + c) 0)) = true := by decide +kernel
theorem vc124_117 : (List.range 13).all (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD (117 + c) 0) (v246.getD (117 + c) 0)) = true := by decide +kernel
theorem vc124_130 : (List.range 3).all (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD (130 + c) 0) (v246.getD (130 + c) 0)) = true := by decide +kernel
theorem vok124 : ∀ c < 133, vCheck 256 (x2KeyMult 1 k124 0 * x2KeyMult 1 k124 1 * x2KeyMult 1 k124 2) (x2KeySize 1 k124) gj246 (x2Trial_246.getD c 0) (v246.getD c 0) = true := by
  intro c hc
  show vCheck 256 2601 225 gj246 (x2Trial_246.getD c 0) (v246.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 13) ∨ (13 ≤ c ∧ c < 26) ∨ (26 ≤ c ∧ c < 39) ∨ (39 ≤ c ∧ c < 52) ∨ (52 ≤ c ∧ c < 65) ∨ (65 ≤ c ∧ c < 78) ∨ (78 ≤ c ∧ c < 91) ∨ (91 ≤ c ∧ c < 104) ∨ (104 ≤ c ∧ c < 117) ∨ (117 ≤ c ∧ c < 130) ∨ (130 ≤ c ∧ c < 133)) with h | h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD c 0) (v246.getD c 0)) 0 13 vc124_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD c 0) (v246.getD c 0)) 13 13 vc124_13 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD c 0) (v246.getD c 0)) 26 13 vc124_26 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD c 0) (v246.getD c 0)) 39 13 vc124_39 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD c 0) (v246.getD c 0)) 52 13 vc124_52 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD c 0) (v246.getD c 0)) 65 13 vc124_65 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD c 0) (v246.getD c 0)) 78 13 vc124_78 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD c 0) (v246.getD c 0)) 91 13 vc124_91 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD c 0) (v246.getD c 0)) 104 13 vc124_104 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD c 0) (v246.getD c 0)) 117 13 vc124_117 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 225 gj246 (x2Trial_246.getD c 0) (v246.getD c 0)) 130 3 vc124_130 c h.1 (by omega)
theorem small124 : x2KeyDegree 1 k124 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k124 0 ∧ 1 ≤ x2KeyMult 1 k124 1 ∧ 1 ≤ x2KeyMult 1 k124 2 ∧ glRowOK 1 (x2KeyTypes 1 k124 0) (x2KeyMult 1 k124 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k124 1) (x2KeyMult 1 k124 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k124 2) (x2KeyMult 1 k124 2) 512 = true ∧ gj246.length = x2KeySize 1 k124 ∧ x2KeySize 1 k124 ≤ 512 ∧ v246.length = 133 := by decide +kernel
theorem chk124 : trialKeyChk 1 k124 133 gj246 x2Trial_246 v246 :=
  trialKeyChk_intro 1 k124 133 gj246 x2Trial_246 v246 small124 gjok124 vok124
def k125 : x2Key 1 := ⟨125, by decide⟩
x2_gj_cols gj247 247 1 3 6 6 256
theorem gjc125_0 : (List.range 39).all (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 (0 + d)) (gj247.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc125_39 : (List.range 39).all (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 (39 + d)) (gj247.getD (39 + d) 0)) = true := by decide +kernel
theorem gjc125_78 : (List.range 39).all (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 (78 + d)) (gj247.getD (78 + d) 0)) = true := by decide +kernel
theorem gjc125_117 : (List.range 39).all (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 (117 + d)) (gj247.getD (117 + d) 0)) = true := by decide +kernel
theorem gjc125_156 : (List.range 39).all (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 (156 + d)) (gj247.getD (156 + d) 0)) = true := by decide +kernel
theorem gjc125_195 : (List.range 13).all (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 (195 + d)) (gj247.getD (195 + d) 0)) = true := by decide +kernel
theorem gjok125 : ∀ d < x2KeySize 1 k125, gjCheck 256 1 (x2KeyTypes 1 k125 0) (x2KeyTypes 1 k125 1) (x2KeyTypes 1 k125 2) (x2KeyMult 1 k125 0) (x2KeyMult 1 k125 1) (x2KeyMult 1 k125 2) (x2JCols (x2KeyGlobal 1 k125) d) (gj247.getD d 0) = true := by
  have hr : x2KeySize 1 k125 = 208 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 d) (gj247.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 39) ∨ (39 ≤ d ∧ d < 78) ∨ (78 ≤ d ∧ d < 117) ∨ (117 ≤ d ∧ d < 156) ∨ (156 ≤ d ∧ d < 195) ∨ (195 ≤ d ∧ d < 208)) with h | h | h | h | h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 d) (gj247.getD d 0)) 0 39 gjc125_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 d) (gj247.getD d 0)) 39 39 gjc125_39 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 d) (gj247.getD d 0)) 78 39 gjc125_78 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 d) (gj247.getD d 0)) 117 39 gjc125_117 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 d) (gj247.getD d 0)) 156 39 gjc125_156 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 6 9 17 17 (x2JCols 247 d) (gj247.getD d 0)) 195 13 gjc125_195 d h.1 (by omega)
x2_v_cols v247 gj247 247 256 2601
theorem vc125_0 : (List.range 14).all (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD (0 + c) 0) (v247.getD (0 + c) 0)) = true := by decide +kernel
theorem vc125_14 : (List.range 14).all (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD (14 + c) 0) (v247.getD (14 + c) 0)) = true := by decide +kernel
theorem vc125_28 : (List.range 14).all (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD (28 + c) 0) (v247.getD (28 + c) 0)) = true := by decide +kernel
theorem vc125_42 : (List.range 14).all (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD (42 + c) 0) (v247.getD (42 + c) 0)) = true := by decide +kernel
theorem vc125_56 : (List.range 14).all (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD (56 + c) 0) (v247.getD (56 + c) 0)) = true := by decide +kernel
theorem vc125_70 : (List.range 14).all (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD (70 + c) 0) (v247.getD (70 + c) 0)) = true := by decide +kernel
theorem vc125_84 : (List.range 14).all (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD (84 + c) 0) (v247.getD (84 + c) 0)) = true := by decide +kernel
theorem vc125_98 : (List.range 14).all (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD (98 + c) 0) (v247.getD (98 + c) 0)) = true := by decide +kernel
theorem vc125_112 : (List.range 14).all (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD (112 + c) 0) (v247.getD (112 + c) 0)) = true := by decide +kernel
theorem vc125_126 : (List.range 7).all (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD (126 + c) 0) (v247.getD (126 + c) 0)) = true := by decide +kernel
theorem vok125 : ∀ c < 133, vCheck 256 (x2KeyMult 1 k125 0 * x2KeyMult 1 k125 1 * x2KeyMult 1 k125 2) (x2KeySize 1 k125) gj247 (x2Trial_247.getD c 0) (v247.getD c 0) = true := by
  intro c hc
  show vCheck 256 2601 208 gj247 (x2Trial_247.getD c 0) (v247.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 14) ∨ (14 ≤ c ∧ c < 28) ∨ (28 ≤ c ∧ c < 42) ∨ (42 ≤ c ∧ c < 56) ∨ (56 ≤ c ∧ c < 70) ∨ (70 ≤ c ∧ c < 84) ∨ (84 ≤ c ∧ c < 98) ∨ (98 ≤ c ∧ c < 112) ∨ (112 ≤ c ∧ c < 126) ∨ (126 ≤ c ∧ c < 133)) with h | h | h | h | h | h | h | h | h | h
  · exact rangeAll_sound (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD c 0) (v247.getD c 0)) 0 14 vc125_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD c 0) (v247.getD c 0)) 14 14 vc125_14 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD c 0) (v247.getD c 0)) 28 14 vc125_28 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD c 0) (v247.getD c 0)) 42 14 vc125_42 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD c 0) (v247.getD c 0)) 56 14 vc125_56 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD c 0) (v247.getD c 0)) 70 14 vc125_70 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD c 0) (v247.getD c 0)) 84 14 vc125_84 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD c 0) (v247.getD c 0)) 98 14 vc125_98 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD c 0) (v247.getD c 0)) 112 14 vc125_112 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 2601 208 gj247 (x2Trial_247.getD c 0) (v247.getD c 0)) 126 7 vc125_126 c h.1 (by omega)
theorem small125 : x2KeyDegree 1 k125 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k125 0 ∧ 1 ≤ x2KeyMult 1 k125 1 ∧ 1 ≤ x2KeyMult 1 k125 2 ∧ glRowOK 1 (x2KeyTypes 1 k125 0) (x2KeyMult 1 k125 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k125 1) (x2KeyMult 1 k125 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k125 2) (x2KeyMult 1 k125 2) 512 = true ∧ gj247.length = x2KeySize 1 k125 ∧ x2KeySize 1 k125 ≤ 512 ∧ v247.length = 133 := by decide +kernel
theorem chk125 : trialKeyChk 1 k125 133 gj247 x2Trial_247 v247 :=
  trialKeyChk_intro 1 k125 133 gj247 x2Trial_247 v247 small125 gjok125 vok125

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k124, ibFS [(v246, v246, 94810963968000)]), (k125, ibFS [(v247, v247, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 6, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN124 : N k124 = x2TrialForm 1 k124) (hN125 : N k125 = x2TrialForm 1 k125) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 6 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k124 133 _ gj246 x2Trial_246 v246 (by decide) (by rw [hN124]; exact trialForm_eq 1 k124 133 x2Trial_246 (by decide) rfl) chk124
  · exact keyOK_of_trialChk 1 N k125 133 _ gj247 x2Trial_247 v247 (by decide) (by rw [hN125]; exact trialForm_eq 1 k125 133 x2Trial_247 (by decide) rfl) chk125

end ThreeCopyQutritWerner.X2.InK1x366
