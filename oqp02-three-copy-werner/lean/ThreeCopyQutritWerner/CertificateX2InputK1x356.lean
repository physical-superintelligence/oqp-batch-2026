module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 5, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x356
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k122 : x2Key 1 := ⟨122, by decide⟩
x2_gj_cols gj244 244 1 3 5 6 256
theorem gjc122_0 : (List.range 95).all (fun d => gjCheck 256 1 3 5 6 9 7 17 (x2JCols 244 (0 + d)) (gj244.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc122_95 : (List.range 82).all (fun d => gjCheck 256 1 3 5 6 9 7 17 (x2JCols 244 (95 + d)) (gj244.getD (95 + d) 0)) = true := by decide +kernel
theorem gjok122 : ∀ d < x2KeySize 1 k122, gjCheck 256 1 (x2KeyTypes 1 k122 0) (x2KeyTypes 1 k122 1) (x2KeyTypes 1 k122 2) (x2KeyMult 1 k122 0) (x2KeyMult 1 k122 1) (x2KeyMult 1 k122 2) (x2JCols (x2KeyGlobal 1 k122) d) (gj244.getD d 0) = true := by
  have hr : x2KeySize 1 k122 = 177 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 5 6 9 7 17 (x2JCols 244 d) (gj244.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 95) ∨ (95 ≤ d ∧ d < 177)) with h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 5 6 9 7 17 (x2JCols 244 d) (gj244.getD d 0)) 0 95 gjc122_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 5 6 9 7 17 (x2JCols 244 d) (gj244.getD d 0)) 95 82 gjc122_95 d h.1 (by omega)
x2_v_cols v244 gj244 244 256 1071
theorem vc122_0 : (List.range 41).all (fun c => vCheck 256 1071 177 gj244 (x2Trial_244.getD (0 + c) 0) (v244.getD (0 + c) 0)) = true := by decide +kernel
theorem vc122_41 : (List.range 41).all (fun c => vCheck 256 1071 177 gj244 (x2Trial_244.getD (41 + c) 0) (v244.getD (41 + c) 0)) = true := by decide +kernel
theorem vc122_82 : (List.range 14).all (fun c => vCheck 256 1071 177 gj244 (x2Trial_244.getD (82 + c) 0) (v244.getD (82 + c) 0)) = true := by decide +kernel
theorem vok122 : ∀ c < 96, vCheck 256 (x2KeyMult 1 k122 0 * x2KeyMult 1 k122 1 * x2KeyMult 1 k122 2) (x2KeySize 1 k122) gj244 (x2Trial_244.getD c 0) (v244.getD c 0) = true := by
  intro c hc
  show vCheck 256 1071 177 gj244 (x2Trial_244.getD c 0) (v244.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 41) ∨ (41 ≤ c ∧ c < 82) ∨ (82 ≤ c ∧ c < 96)) with h | h | h
  · exact rangeAll_sound (fun c => vCheck 256 1071 177 gj244 (x2Trial_244.getD c 0) (v244.getD c 0)) 0 41 vc122_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 1071 177 gj244 (x2Trial_244.getD c 0) (v244.getD c 0)) 41 41 vc122_41 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 1071 177 gj244 (x2Trial_244.getD c 0) (v244.getD c 0)) 82 14 vc122_82 c h.1 (by omega)
theorem small122 : x2KeyDegree 1 k122 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k122 0 ∧ 1 ≤ x2KeyMult 1 k122 1 ∧ 1 ≤ x2KeyMult 1 k122 2 ∧ glRowOK 1 (x2KeyTypes 1 k122 0) (x2KeyMult 1 k122 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k122 1) (x2KeyMult 1 k122 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k122 2) (x2KeyMult 1 k122 2) 512 = true ∧ gj244.length = x2KeySize 1 k122 ∧ x2KeySize 1 k122 ≤ 512 ∧ v244.length = 96 := by decide +kernel
theorem chk122 : trialKeyChk 1 k122 96 gj244 x2Trial_244 v244 :=
  trialKeyChk_intro 1 k122 96 gj244 x2Trial_244 v244 small122 gjok122 vok122

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k122, ibFS [(v244, v244, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 5, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN122 : N k122 = x2TrialForm 1 k122) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 5 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k122 96 _ gj244 x2Trial_244 v244 (by decide) (by rw [hN122]; exact trialForm_eq 1 k122 96 x2Trial_244 (by decide) rfl) chk122

end ThreeCopyQutritWerner.X2.InK1x356
